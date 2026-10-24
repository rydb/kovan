-------------------------------- MODULE Mvcc --------------------------------
(***************************************************************************)
(* kovan-mvcc (kovan-mvcc/src/percolator.rs, storage.rs,                    *)
(* timestamp_oracle.rs) at the grain of its atomic steps.                   *)
(*                                                                          *)
(* Each process is one transaction running a fixed program (MC_Mvcc.tla):   *)
(* its isolation level, its reads, writes and deletes, and its end (commit  *)
(* or drop). A transaction takes its start_ts from the oracle (one          *)
(* fetch-add), buffers its writes, and reads a key by loading the key's     *)
(* lock, then its latest Put or Delete record at or before the read's       *)
(* timestamp, then the data that record names. A lock of a transaction that *)
(* started at or before the read's timestamp makes the read back off and    *)
(* look again, or give up and answer None. Commit takes the locks of the    *)
(* written keys in sorted order (insert_if_absent), checks each key's       *)
(* latest record against start_ts, writes the data, validates a             *)
(* Serializable read set under the global SSI lock, takes the commit_ts,    *)
(* writes the primary's record and drops its lock, then each secondary's.   *)
(* A failed validation rolls the keys back: lock, data, then a Rollback     *)
(* record at start_ts. Nothing in the crate resolves another transaction's  *)
(* lock.                                                                    *)
(*                                                                          *)
(* The embedder's parts of the crate are processes of their own: a caller   *)
(* of safe_read_ts (the in-flight writer registry, external-apply mode),    *)
(* and a garbage collector calling gc_writes and gc_data with a watermark   *)
(* from min_active_ts or one it computes soundly.                           *)
(*                                                                          *)
(* Every call into a kovan_map map is one step, as the chained and          *)
(* hopscotch families prove it linearizable (proofs/tla/chained,            *)
(* proofs/tla/hopscotch); a walk of a map is two steps, its start and its   *)
(* end, and yields every entry present for its whole length and any of the *)
(* entries present at some moment of it (the families' WalkExact). Each     *)
(* version-chain call (put_write, get_latest_write, get_latest_commit,      *)
(* put_data, get_data, delete_data, gc_writes, gc_data) is one step: its    *)
(* critical section under the key's mutex, the outer map's entry for the    *)
(* key being created once and never removed. A thread's own work between    *)
(* two shared steps is one step. Values are the writing transaction's id;   *)
(* the setup transaction 0 committed the keys in Seeded (start 1, commit 2).*)
(*                                                                          *)
(* `Mutation` puts back one wrong rule at a time; see README.md.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Keys,         \* the keys, integers in the order the code sorts their bytes
    Plan,         \* each transaction's [iso, ops, fin]: isolation, operations, commit or drop
    Seeded,       \* the keys transaction 0 committed before the others began
    ExtApply,     \* external-apply mode: the embedder registers each writer in flight
    Hz,           \* {} or the id of the embedder's safe_read_ts caller
    HzRounds,     \* the calls it makes
    SpinCap,      \* SPIN_CAP (40 in the code)
    ScanRetries,  \* SCAN_RETRIES (64 in the code)
    Gc,           \* {} or the id of the embedder's garbage collector
    GcRounds,     \* the passes it makes
    Watermark,    \* "registry": min_active_ts; "sound": any watermark no live reader is below
    Mutation      \* "none", or one wrong rule put back

NONE == -1
\* u64::MAX, the bound of the records get_latest_write(key, u64::MAX) reads.
INF == 1000
NoRec == [ts |-> 0, st |-> 0, kind |-> "none"]
NoData == [st |-> 0, val |-> NONE]
Txns == DOMAIN Plan
AllTx == Txns \cup {0}
Iso(t) == Plan[t].iso
NOps(t) == Len(Plan[t].ops)
OpOf(t, j) == Plan[t].ops[j].op
OpK(t, j) == Plan[t].ops[j].key
Min2(a, b) == IF a < b THEN a ELSE b
Max2(a, b) == IF a > b THEN a ELSE b
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y
RECURSIVE Ascending(_)
Ascending(S) == IF S = {} THEN <<>> ELSE <<MinOf(S)>> \o Ascending(S \ {MinOf(S)})

\* The buffer `writes` before operation j: each key's last write or delete.
RECURSIVE Buf(_, _)
Buf(t, j) ==
    IF j = 1 THEN [k \in Keys |-> "none"]
    ELSE IF OpOf(t, j - 1) = "w" THEN [Buf(t, j - 1) EXCEPT ![OpK(t, j - 1)] = "put"]
    ELSE IF OpOf(t, j - 1) = "d" THEN [Buf(t, j - 1) EXCEPT ![OpK(t, j - 1)] = "del"]
    ELSE Buf(t, j - 1)
BufT == [t \in Txns |-> [j \in 1 .. NOps(t) + 1 |-> Buf(t, j)]]
FinalBuf == [t \in AllTx |->
                IF t = 0 THEN [k \in Keys |-> IF k \in Seeded THEN "put" ELSE "none"]
                ELSE BufT[t][NOps(t) + 1]]
WSet == [t \in AllTx |-> {k \in Keys : FinalBuf[t][k] # "none"}]
PutKeys(t) == {k \in Keys : FinalBuf[t][k] = "put"}
WIdx(t) == {j \in 1 .. NOps(t) : OpOf(t, j) \in {"w", "d"}}
\* primary_key: the first key written or deleted.
Primary == [t \in Txns |-> IF WIdx(t) = {} THEN 0 ELSE OpK(t, MinOf(WIdx(t)))]
FirstW == [t \in Txns |-> IF WIdx(t) = {} THEN 0 ELSE MinOf(WIdx(t))]
\* read_set (Serializable): every key read, from the buffer or not.
RSet == [t \in Txns |-> {OpK(t, j) : j \in {j \in 1 .. NOps(t) : OpOf(t, j) = "r"}}]
\* The next operation that needs a shared step: a read of a key not in the buffer.
RECURSIVE NextS(_, _)
NextS(t, j) ==
    IF j > NOps(t) THEN j
    ELSE IF OpOf(t, j) = "r" /\ BufT[t][j][OpK(t, j)] = "none" THEN j
    ELSE NextS(t, j + 1)
NextT == [t \in Txns |-> [j \in 1 .. NOps(t) + 1 |-> NextS(t, j)]]

\* The version chains: a BTreeMap keyed by timestamp, whose insert replaces.
Below(S, ts) == {r \in S : r.ts <= ts}
LatestWrite(S, ts) ==
    IF Below(S, ts) = {} THEN NoRec
    ELSE CHOOSE r \in Below(S, ts) : \A q \in Below(S, ts) : q.ts <= r.ts
LatestCommit(S, ts) == LatestWrite({r \in S : r.kind # "rb"}, ts)
PutRec(S, r) == {q \in S : q.ts # r.ts} \cup {r}
PutData(D, s, v) == {d \in D : d.st # s} \cup {[st |-> s, val |-> v]}
DataAt(D, s) == IF \E d \in D : d.st = s THEN (CHOOSE d \in D : d.st = s).val ELSE NONE
LatestData(D, ts) ==
    IF {d \in D : d.st <= ts} = {} THEN NoData
    ELSE CHOOSE d \in D : d.st <= ts /\ \A e \in D : e.st <= ts => e.st <= d.st
\* giveup_answers_none: the code before this fix: a read whose backoff gives up answers None, as
\* for a key that holds no value (GiveUpSound).
MutGiveUpNone == Mutation = "giveup_answers_none"
\* ssi_latest_record: the SSI validation reads each key's latest record, which a Rollback record
\* can be, hiding the commit under it (SerialReads).
MutSsiRecord == Mutation = "ssi_latest_record"
\* gc_keeps_latest_record: gc_writes keeps the latest record at or below the watermark of any
\* kind, a Rollback record too, and drops the commit under it (SnapshotRead).
MutGcRecord == Mutation = "gc_keeps_latest_record"
\* gc_keeps_latest_data: gc_data keeps the latest data at or below the watermark, a prewrite's
\* too, and drops the committed data under it (VersionData).
MutGcData == Mutation = "gc_keeps_latest_data"
\* register_after_ts: begin takes start_ts, then registers it (WatermarkSound).
MutRegAfter == Mutation = "register_after_ts"
\* walk_only: the watermark is min_active_ts's walk alone, with no bound taken before it, and no
\* pass on an empty registry (WatermarkSound).
MutWalkOnly == Mutation = "walk_only"
\* unregister_first: commit unregisters at its start and Drop before its rollback, as before this
\* fix; with the GC passes fixed no property tells it apart (MV_inert_unregister_first, expected
\* to pass).
MutUnregFirst == Mutation = "unregister_first"

\* gc_writes and gc_data keep the latest commit at or below the watermark, and every record and
\* every data version at or above it (the mutations: the latest of any kind).
GcWrites(S, w) ==
    LET keep == IF MutGcRecord THEN LatestWrite(S, w) ELSE LatestCommit(S, w)
    IN IF keep = NoRec THEN S ELSE {r \in S : r.ts >= keep.ts}
GcData(D, S, w) ==
    IF MutGcData
    THEN LET keep == LatestData(D, w) IN IF keep = NoData THEN D ELSE {d \in D : d.st >= keep.st}
    ELSE LET keep == LatestCommit(S, w) IN IF keep = NoRec THEN D ELSE {d \in D : d.st >= keep.st}
MinOpt(a, b) == IF a = NONE THEN b ELSE IF b = NONE THEN a ELSE Min2(a, b)

\* oracle_load_store: get_timestamp as a load and a store instead of a fetch-add, at begin
\* (TsIncreasing).
MutOracle == Mutation = "oracle_load_store"
\* read_ignores_lock: a read goes to the write column without looking at the key's lock
\* (SnapshotRead).
MutIgnoreLock == Mutation = "read_ignores_lock"
\* read_data_column: a read answers the latest data at or below its timestamp, without the
\* write column (NoDirtyRead).
MutDataColumn == Mutation = "read_data_column"
\* skip_newer_commit: pass 2 checks only for a rollback record (FirstCommitterWins).
MutSkipNewer == Mutation = "skip_newer_commit"
\* check_before_lock: pass 2 (the conflict check) runs before pass 1 (the locks)
\* (FirstCommitterWins).
MutCheckFirst == Mutation = "check_before_lock"
\* lock_get_then_insert: put_lock as a get, then an insert (FirstCommitterWins).
MutLockSplit == Mutation = "lock_get_then_insert"
\* secondaries_first: commit writes the secondaries' records before the primary's
\* (PrimaryDecides).
MutSecFirst == Mutation = "secondaries_first"
\* validate_after_primary: the SSI validation runs after the primary committed (AllOrNothing).
MutLateCheck == Mutation = "validate_after_primary"
\* no_ssi_lock: the SSI validation and commit run without ssi_commit_lock (SerialReads).
MutNoSsiLock == Mutation = "no_ssi_lock"
\* rollback_keeps_data: rollback leaves the key's data at start_ts (NoLeak).
MutKeepData == Mutation = "rollback_keeps_data"
\* rollback_deletes_range: rollback's delete_data drops every version at or below its start_ts
\* (VersionData).
MutRange == Mutation = "rollback_deletes_range"
\* ssi_lock_kept: a failed validation returns without dropping the SSI guard (Termination).
MutKeepSsi == Mutation = "ssi_lock_kept"
\* secondary_keeps_lock: commit_secondaries writes a secondary's record and leaves its lock
\* (LocksReleased).
MutSecKeepsLock == Mutation = "secondary_keeps_lock"
\* ext_commit_unregisters: commit unregisters the writer in external-apply mode (SafeReadTs).
MutExtUnreg == Mutation = "ext_commit_unregisters"
\* cap_returns_now: past the spin cap safe_read_ts answers oracle_now (SafeReadTs).
MutCapNow == Mutation = "cap_returns_now"
\* read_waits: a read that meets a lock looks again until it is gone, never giving up
\* (ReadersEnd).
MutReadWaits == Mutation = "read_waits"
\* spin_unbounded: safe_read_ts spins while a writer is at or below oracle_now, with no cap
\* (ReadersEnd).
MutSpinForever == Mutation = "spin_unbounded"
\* epoch_ignored, a rule put back that no property tells apart (MV_inert_epoch_ignored, expected
\* to pass): register bumps the epoch before its insert, and min_ts trusts every pass without its
\* second epoch load.
MutNoEpoch == Mutation = "epoch_ignored"

(* --algorithm Mvcc
variables
    \* the oracle's counter; hiTs, the greatest timestamp it handed out
    clock = IF Seeded = {} THEN 0 ELSE 2,
    hiTs = IF Seeded = {} THEN 0 ELSE 2,
    \* CF_LOCK: the holder of each key's lock (0: none)
    lock = [k \in Keys |-> 0],
    \* CF_WRITE: each key's records [ts, st (the start_ts it names), kind]
    wr = [k \in Keys |-> IF k \in Seeded THEN {[ts |-> 2, st |-> 1, kind |-> "put"]} ELSE {}],
    \* CF_DATA: each key's data [st, val]
    data = [k \in Keys |-> IF k \in Seeded THEN {[st |-> 1, val |-> 0]} ELSE {}],
    startTs = [t \in AllTx |-> IF t = 0 THEN 1 ELSE 0],
    commitTs = [t \in AllTx |-> IF t = 0 /\ Seeded # {} THEN 2 ELSE 0],
    \* the read timestamp of a read in progress
    readTs = [t \in Txns |-> 0],
    \* the transactions whose primary record was written
    cdone = {},
    \* the instance's greatest timestamp taken (KovanMVCC::issued: begin, a ReadCommitted read,
    \* commit), and the value the registry holds for each transaction
    issued = IF Seeded = {} THEN 0 ELSE 2,
    regTs = [t \in Txns |-> 0],
    \* ActiveTxnRegistry, and the GC's walk of it: present throughout, present at some moment
    active = {}, gThru = {}, gEver = {},
    \* InflightWriteRegistry and its insert_epoch, and the safe_read_ts caller's walk of it
    inflight = {}, epoch = 0, hThru = {}, hEver = {},
    \* ssi_commit_lock's holder (0: free)
    ssi = 0,
    \* the checks that failed
    errs = {};

define
    GcOn == Gc # {}
    GcWalking == \E g \in Gc : pc[g] = "GC1"
    HzWalking == \E x \in Hz : pc[x] = "HZ3"
    TsErr(v) == IF v <= hiTs THEN {"ts"} ELSE {}
    \* The snapshot at r of key k: the value of the transaction with the greatest commit_ts at or
    \* before r among those that wrote k (none: NONE); a Delete is NONE.
    CommittedIn(k, r) ==
        {w \in AllTx : commitTs[w] # 0 /\ commitTs[w] <= r /\ FinalBuf[w][k] # "none"}
    SnapVal(k, r) ==
        IF CommittedIn(k, r) = {} THEN NONE
        ELSE LET w == CHOOSE w \in CommittedIn(k, r) :
                          \A v \in CommittedIn(k, r) : commitTs[v] <= commitTs[w]
             IN IF FinalBuf[w][k] = "put" THEN w ELSE NONE
    \* SnapshotRead and NoDirtyRead at a read's answer.
    ReadErr(k, r, a) ==
        (IF a # SnapVal(k, r) THEN {"stale"} ELSE {})
            \cup (IF a # NONE /\ ~(commitTs[a] # 0 /\ commitTs[a] <= r) THEN {"dirty"} ELSE {})
    \* SerialReads at a Serializable commit_ts: no Serializable transaction committed a key of its
    \* read set since its start.
    SerErr(t) ==
        IF Iso(t) = "SER" /\ \E w \in Txns \ {t} :
               Iso(w) = "SER" /\ commitTs[w] > startTs[t] /\ RSet[t] \cap WSet[w] # {}
        THEN {"serial"} ELSE {}
    \* A transaction that may still read, and the timestamp its reads need versions at.
    ReadPhase == {"BG2", "OP", "XR1", "XR2", "RO", "RL", "RW", "RD"}
    Live(t) == startTs[t] # 0 /\ pc[t] \in ReadPhase
    NeedTs(t) ==
        IF Iso(t) = "RC" THEN (IF readTs[t] # 0 THEN readTs[t] ELSE clock + 1) ELSE startTs[t]
    SoundMax == MinOf({NeedTs(t) : t \in {u \in Txns : Live(u)}} \cup {clock + 1})
    \* WatermarkSound at the GC's watermark.
    WmErr(w) == IF \E t \in Txns : Live(t) /\ w > NeedTs(t) THEN {"watermark"} ELSE {}
    MinStart(Y) == IF Y = {} THEN NONE ELSE MinOf({startTs[t] : t \in Y})
    MinReg(Y) == IF Y = {} THEN NONE ELSE MinOf({regTs[t] : t \in Y})
    \* SafeReadTs at safe_read_ts's answer: no writer with a commit_ts at or below it is still
    \* being applied (it has not returned from mark_txn_applied).
    HzErr(hv) ==
        IF \E w \in Txns : commitTs[w] # 0 /\ commitTs[w] <= hv /\ pc[w] # "Done"
        THEN {"horizon"} ELSE {}
end define;

\* ---------------------------------------------------------------- a transaction
process Tx \in Txns
variables i = 1, todo = <<>>, acq = <<>>, left = {}, rc = NoRec, ck = 0, ld = 0;
begin
BG0: \* begin_with_isolation: active_txns.register(txn_id, issued), before start_ts is taken
    \* (register_after_ts: no such step)
    if GcOn /\ ~MutRegAfter then
        active := active \cup {self} || regTs[self] := issued
            || gEver := IF GcWalking THEN gEver \cup {self} ELSE gEver;
    end if;
BG1: \* start_ts = ts_oracle.get_timestamp(), the counter's fetch-add, and issued's fetch_max
    if MutOracle then
        ld := clock;
        goto BG1b;
    else
        startTs[self] := clock + 1 || clock := clock + 1 || hiTs := Max2(hiTs, clock + 1)
            || issued := Max2(issued, clock + 1) || errs := errs \cup TsErr(clock + 1);
        if GcOn then goto BG2; else goto OP; end if;
    end if;
BG1b: \* (oracle_load_store) the store of the value loaded, plus one
    startTs[self] := ld + 1 || clock := ld + 1 || hiTs := Max2(hiTs, ld + 1)
        || issued := Max2(issued, ld + 1) || errs := errs \cup TsErr(ld + 1);
    ld := 0;
    if GcOn then goto BG2; else goto OP; end if;
BG2: \* active_txns.register(txn_id, start_ts): the entry's value replaced (register_after_ts: the
     \* entry inserted)
    active := active \cup {self} || regTs[self] := startTs[self]
        || gEver := IF GcWalking THEN gEver \cup {self} ELSE gEver;
OP: \* the thread's own work up to its next shared step: the buffered writes and deletes, the
    \* reads of keys in the buffer (writes.get); then the next read, or the end
    with j = NextT[self][i] do
        i := j;
        if ExtApply /\ FirstW[self] # 0 /\ FirstW[self] < j /\ self \notin inflight then
            goto XR1;
        elsif j <= NOps(self) then
            if Iso(self) = "RC" then
                goto RO;
            else
                readTs[self] := startTs[self];
                goto RL;
            end if;
        elsif Plan[self].fin = "drop" then
            if GcOn /\ MutUnregFirst then goto DR1;
            elsif self \in inflight then goto DR2;
            elsif GcOn then goto DR1;
            else goto Done;
            end if;
        elsif GcOn then
            goto CM0;
        elsif WSet[self] = {} then
            goto Done;
        elsif MutCheckFirst then
            todo := Ascending(WSet[self]);
            goto PC;
        else
            todo := Ascending(WSet[self]);
            goto PL;
        end if;
    end with;
XR1: \* the embedder registers the writer at its first write: inflight_writes.register's insert
    if MutNoEpoch then
        epoch := epoch + 1;
    else
        inflight := inflight \cup {self} || hEver := IF HzWalking THEN hEver \cup {self} ELSE hEver;
    end if;
XR2: \* register's insert_epoch.fetch_add(1), after the insert
    if MutNoEpoch then
        inflight := inflight \cup {self} || hEver := IF HzWalking THEN hEver \cup {self} ELSE hEver;
    else
        epoch := epoch + 1;
    end if;
    goto OP;

\* ---------------------------------------------------------------- read
RO: \* ReadCommitted: read_ts = ts_oracle.get_timestamp()
    readTs[self] := clock + 1 || clock := clock + 1 || hiTs := Max2(hiTs, clock + 1)
        || issued := Max2(issued, clock + 1) || errs := errs \cup TsErr(clock + 1);
RL: \* storage.get_lock(key): a lock of a transaction that started at or before read_ts
    with k = OpK(self, i), hd = lock[k] do
        if hd # 0 /\ startTs[hd] <= readTs[self] /\ ~MutIgnoreLock then
            if hd = self then
                \* read-your-own-writes after prewrite: unreachable, commit consumes the Txn
                i := i + 1;
                readTs[self] := 0;
                goto OP;
            else
                either
                    \* BackoffAction::Yield or Retry: look again
                    goto RL;
                or
                    await ~MutReadWaits;
                    \* BackoffAction::Abort: Err(LockConflict), no answer (giveup_answers_none:
                    \* None, the answer for a key that holds no value)
                    errs := errs \cup (IF MutGiveUpNone /\ SnapVal(k, readTs[self]) # NONE
                                       THEN {"giveup"} ELSE {});
                    i := i + 1;
                    readTs[self] := 0;
                    goto OP;
                end either;
            end if;
        else
            goto RW;
        end if;
    end with;
RW: \* storage.get_latest_commit(key, read_ts): the latest Put or Delete record at or before it
    with k = OpK(self, i), r = LatestCommit(wr[k], readTs[self]) do
        if MutDataColumn then
            errs := errs \cup ReadErr(k, readTs[self], LatestData(data[k], readTs[self]).val);
            i := i + 1;
            readTs[self] := 0;
            goto OP;
        elsif r.kind = "put" then
            rc := r;
            goto RD;
        else
            errs := errs \cup ReadErr(k, readTs[self], NONE);
            i := i + 1;
            readTs[self] := 0;
            goto OP;
        end if;
    end with;
RD: \* storage.get_data(key, write_info.start_ts)
    with k = OpK(self, i), v = DataAt(data[k], rc.st) do
        if v = NONE then
            \* the data is gone: the read answers Err(StorageError)
            errs := errs \cup (IF SnapVal(k, readTs[self]) # NONE THEN {"lost"} ELSE {});
        else
            errs := errs \cup ReadErr(k, readTs[self], v);
        end if;
        i := i + 1;
        readTs[self] := 0;
        rc := NoRec;
        goto OP;
    end with;

\* ---------------------------------------------------------------- end: drop
DR1: \* Drop of an uncommitted Txn: active_txns.unregister(txn_id), after its rollback
     \* (unregister_first: before it)
    active := active \ {self} || gThru := gThru \ {self};
    if MutUnregFirst /\ self \in inflight then goto DR2; else goto Done; end if;
DR2: \* rollback(): inflight_writes.unregister (its lock loads find no lock of its own)
    inflight := inflight \ {self} || hThru := hThru \ {self};
    if GcOn /\ ~MutUnregFirst then goto DR1; else goto Done; end if;

\* ---------------------------------------------------------------- end: commit
CM0: \* commit(): committed = true (unregister_first: active_txns.unregister(txn_id) here, not at
     \* the commit's end, UR)
    if MutUnregFirst then active := active \ {self} || gThru := gThru \ {self}; end if;
    if WSet[self] = {} then
        goto UR;
    elsif MutCheckFirst then
        todo := Ascending(WSet[self]);
        goto PC;
    else
        todo := Ascending(WSet[self]);
        goto PL;
    end if;
PL: \* prewrite pass 1: storage.put_lock(key), locks.insert_if_absent, keys sorted
    with k = Head(todo) do
        if lock[k] # 0 /\ lock[k] # self then
            \* LockConflict: release the locks taken so far
            todo := <<>>;
            if acq # <<>> then
                goto PF;
            else
                acq := <<>>;
                if self \in inflight then goto RBP; else goto UR; end if;
            end if;
        elsif MutLockSplit then
            goto PL2;
        else
            \* acquired (a lock of its own is overwritten: unreachable, a key is locked once)
            lock[k] := self;
            if Len(todo) > 1 then
                acq := Append(acq, k);
                todo := Tail(todo);
                goto PL;
            elsif ~MutCheckFirst then
                acq := Append(acq, k);
                todo := Ascending(WSet[self]);
                goto PC;
            elsif PutKeys(self) # {} then
                todo := Ascending(PutKeys(self));
                acq := <<>>;
                goto PD;
            elsif Iso(self) = "SER" then
                todo := <<>>;
                acq := <<>>;
                goto SL;
            else
                todo := <<>>;
                acq := <<>>;
                goto CT;
            end if;
        end if;
    end with;
PL2: \* (lock_get_then_insert) the insert, after the get found no other lock
    with k = Head(todo) do
        lock[k] := self;
        acq := Append(acq, k);
        if Len(todo) > 1 then
            todo := Tail(todo);
            goto PL;
        else
            todo := Ascending(WSet[self]);
            goto PC;
        end if;
    end with;
PF: \* the failed prewrite's storage.delete_lock of each lock taken, in the order taken
    lock[Head(acq)] := 0;
    if Len(acq) > 1 then
        acq := Tail(acq);
        goto PF;
    else
        acq := <<>>;
        if self \in inflight then goto RBP; else goto UR; end if;
    end if;
RBP: \* commit's rollback() after a failed prewrite: inflight_writes.unregister (its lock loads
     \* find no lock of its own)
    inflight := inflight \ {self} || hThru := hThru \ {self};
    goto UR;
PC: \* prewrite pass 2: storage.get_latest_write(key, u64::MAX) against start_ts
    with k = Head(todo), r = LatestWrite(wr[k], INF) do
        if r.kind # "none" /\ r.ts >= startTs[self] /\ (r.kind = "rb" \/ ~MutSkipNewer) then
            \* RollbackRecord or WriteConflict: release the locks taken
            todo := <<>>;
            if acq # <<>> then
                goto PF;
            else
                acq := <<>>;
                if self \in inflight then goto RBP; else goto UR; end if;
            end if;
        elsif Len(todo) > 1 then
            todo := Tail(todo);
            goto PC;
        elsif MutCheckFirst then
            todo := Ascending(WSet[self]);
            goto PL;
        elsif PutKeys(self) # {} then
            todo := Ascending(PutKeys(self));
            acq := <<>>;
            goto PD;
        elsif Iso(self) = "SER" /\ ~MutLateCheck then
            todo := <<>>;
            acq := <<>>;
            goto SL;
        else
            todo := <<>>;
            acq := <<>>;
            goto CT;
        end if;
    end with;
PD: \* prewrite pass 3: storage.put_data(key, start_ts, value) for each Put
    with k = Head(todo) do
        data[k] := PutData(data[k], startTs[self], self);
        if Len(todo) > 1 then
            todo := Tail(todo);
            goto PD;
        elsif Iso(self) = "SER" /\ ~MutLateCheck then
            todo := <<>>;
            goto SL;
        else
            todo := <<>>;
            goto CT;
        end if;
    end with;
SL: \* Serializable: ssi_commit_lock.lock()
    await ssi = 0 \/ MutNoSsiLock;
    if ~MutNoSsiLock then ssi := self; end if;
    if RSet[self] # {} then
        left := RSet[self];
        goto SV;
    elsif ~MutLateCheck then
        goto CT;
    elsif WSet[self] \ {Primary[self]} # {} then
        left := WSet[self] \ {Primary[self]};
        goto CS1;
    elsif ssi = self then
        goto CE;
    elsif ExtApply then
        goto URX;
    else
        goto UR;
    end if;
SV: \* SSI validation: storage.get_latest_commit(key, u64::MAX) for each key of the read set
    \* (ssi_latest_record: get_latest_write, the latest record of any kind)
    with k \in left, r = IF MutSsiRecord THEN LatestWrite(wr[k], INF) ELSE LatestCommit(wr[k], INF) do
        if r.kind \in {"put", "del"} /\ r.ts > startTs[self] then
            \* SerializationFailure: roll back; the guard is dropped at the return
            if ExtApply then
                left := {};
                goto RB0;
            else
                left := WSet[self];
                goto RB1;
            end if;
        elsif left # {k} then
            left := left \ {k};
            goto SV;
        elsif ~MutLateCheck then
            left := {};
            goto CT;
        elsif WSet[self] \ {Primary[self]} # {} then
            left := WSet[self] \ {Primary[self]};
            goto CS1;
        elsif ssi = self then
            left := {};
            goto CE;
        elsif ExtApply then
            left := {};
            goto URX;
        else
            left := {};
            goto UR;
        end if;
    end with;
CT: \* commit_ts = ts_oracle.get_timestamp()
    commitTs[self] := clock + 1 || clock := clock + 1 || hiTs := Max2(hiTs, clock + 1)
        || issued := Max2(issued, clock + 1)
        || errs := errs \cup TsErr(clock + 1) \cup SerErr(self);
    if MutSecFirst /\ WSet[self] \ {Primary[self]} # {} then
        left := WSet[self] \ {Primary[self]};
        goto CS1;
    end if;
CP1: \* commit_primary: storage.get_lock(primary), which must be this transaction's
    if lock[Primary[self]] # self then
        \* PrimaryLockMissing or PrimaryLockMismatch: commit unregisters, then rolls back
        errs := errs \cup {"primary"};
        if ExtApply then goto RB0; else left := WSet[self]; goto RB1; end if;
    end if;
CP2: \* storage.put_write(primary, commit_ts, its start_ts and kind): the transaction commits
    wr[Primary[self]] := PutRec(wr[Primary[self]],
                                [ts |-> commitTs[self], st |-> startTs[self],
                                 kind |-> FinalBuf[self][Primary[self]]])
        || cdone := cdone \cup {self};
CP3: \* storage.delete_lock(primary)
    lock[Primary[self]] := 0;
    if Iso(self) = "SER" /\ MutLateCheck then
        goto SL;
    elsif ~MutSecFirst /\ WSet[self] \ {Primary[self]} # {} then
        left := WSet[self] \ {Primary[self]};
        goto CS1;
    elsif ssi = self \/ (MutExtUnreg /\ self \in inflight) then
        goto CE;
    elsif ExtApply then
        goto URX;
    else
        goto UR;
    end if;
CS1: \* commit_secondaries, in the buffer's order: storage.put_write(key, commit_ts, ...)
    with k \in left do
        wr[k] := PutRec(wr[k], [ts |-> commitTs[self], st |-> startTs[self],
                                kind |-> FinalBuf[self][k]]);
        ck := k;
    end with;
CS2: \* storage.get_lock(key): the lock is cleaned up if it is still this transaction's
    if lock[ck] = self /\ ~MutSecKeepsLock then
        goto CS3;
    else
        left := left \ {ck};
        ck := 0;
        if left # {} then goto CS1;
        elsif MutSecFirst then goto CP1;
        elsif ssi = self \/ (MutExtUnreg /\ self \in inflight) then goto CE;
        elsif ExtApply then goto URX;
        else goto UR;
        end if;
    end if;
CS3: \* storage.delete_lock(key)
    lock[ck] := 0;
    left := left \ {ck};
    ck := 0;
    if left # {} then goto CS1;
    elsif MutSecFirst then goto CP1;
    elsif ssi = self \/ (MutExtUnreg /\ self \in inflight) then goto CE;
    elsif ExtApply then goto URX;
    else goto UR;
    end if;
CE: \* commit's end: inflight_writes.unregister when not external-apply (only
    \* ext_commit_unregisters reaches it with a writer registered), and the SSI guard dropped
    if ssi = self then ssi := 0; end if;
    if MutExtUnreg then inflight := inflight \ {self} || hThru := hThru \ {self}; end if;
    if ExtApply /\ self \in cdone then goto URX; else goto UR; end if;
XA: \* the embedder applies the writes, then mark_txn_applied(txn_id): inflight_writes.unregister
    inflight := inflight \ {self} || hThru := hThru \ {self};
    goto Done;

\* ---------------------------------------------------------------- rollback
UR: \* commit's end, or its rollback's: active_txns.unregister(txn_id), once its data is committed or
    \* rolled back (unregister_first: done at CM0)
    if ~MutUnregFirst then active := active \ {self} || gThru := gThru \ {self}; end if;
    goto Done;
URX: \* the same, then the embedder's apply
    if ~MutUnregFirst then active := active \ {self} || gThru := gThru \ {self}; end if;
    goto XA;

RB0: \* rollback(): inflight_writes.unregister (after a failed commit_primary, commit's own
     \* unregister just before it, a second removal of the same entry)
    inflight := inflight \ {self} || hThru := hThru \ {self};
    left := WSet[self];
RB1: \* storage.get_lock(key), for each key of the buffer in its order
    with k \in left do
        if lock[k] = self then
            ck := k;
            goto RB2;
        else
            left := left \ {k};
            if left # {} then goto RB1;
            elsif ssi = self /\ ~MutKeepSsi then goto CE;
            else goto UR;
            end if;
        end if;
    end with;
RB2: \* storage.delete_lock(key)
    lock[ck] := 0;
    if MutKeepData then goto RB4; end if;
RB3: \* storage.delete_data(key, start_ts)
    data[ck] := IF MutRange THEN {d \in data[ck] : d.st > startTs[self]}
                ELSE {d \in data[ck] : d.st # startTs[self]};
RB4: \* storage.put_write(key, start_ts, Rollback): no resurrection of this start_ts
    wr[ck] := PutRec(wr[ck], [ts |-> startTs[self], st |-> startTs[self], kind |-> "rb"]);
    left := left \ {ck};
    ck := 0;
    if left # {} then goto RB1;
    elsif ssi = self /\ ~MutKeepSsi then goto CE;
    else goto UR;
    end if;
end process;

\* ---------------------------------------------------------------- the embedder's safe_read_ts
process Horizon \in Hz
variables now = 0, att = 0, scans = 0, cons = NONE, bef = 0, mn = NONE, h = 0, rd = 0;
begin
HZ0: \* oracle_now = ts_oracle.get_timestamp(), then safe_read_ts(oracle_now)
    if rd >= HzRounds then
        now := 0;
        att := 0;
        h := 0;
        goto Done;
    else
        now := clock + 1 || clock := clock + 1 || hiTs := Max2(hiTs, clock + 1)
            || errs := errs \cup TsErr(clock + 1);
        att := 0;
        h := 0;
        rd := rd + 1;
    end if;
HZ1: \* min_ts: a pass loads insert_epoch
    bef := epoch;
HZ2: \* the pass's walk of the writers begins
    hThru := inflight || hEver := inflight;
HZ3: \* the walk ends: the least start_ts among the writers it yielded
    with Y \in {Y \in SUBSET hEver : hThru \subseteq Y} do
        mn := MinStart(Y);
    end with;
    hThru := {} || hEver := {};
HZ4: \* insert_epoch loaded again: a stable pass answers; an unstable one is merged into the
     \* least value seen, and after SCAN_RETRIES passes that answers
    if epoch # bef /\ ~MutNoEpoch /\ scans + 1 < ScanRetries then
        cons := MinOpt(cons, mn) || scans := scans + 1 || mn := NONE || bef := 0;
        goto HZ1;
    else
        with m = IF epoch = bef \/ MutNoEpoch THEN mn ELSE MinOpt(cons, mn) do
            cons := NONE || scans := 0 || mn := NONE || bef := 0;
            if m = NONE \/ m > now then
                \* no writer at or below oracle_now: the horizon is oracle_now
                h := now || errs := errs \cup HzErr(now);
                goto HZ0;
            elsif att >= SpinCap /\ ~MutSpinForever then
                \* past the spin cap: strictly below the oldest writer (saturating_sub)
                with hv = IF MutCapNow THEN now ELSE Min2(now, Max2(m - 1, 0)) do
                    h := hv || errs := errs \cup HzErr(hv);
                end with;
                goto HZ0;
            else
                \* the TTAS spin: the PAUSE loop, then min_ts again
                att := IF MutSpinForever THEN att ELSE att + 1;
                goto HZ1;
            end if;
        end with;
    end if;
end process;

\* ---------------------------------------------------------------- the embedder's GC
process Collector \in Gc
variables wm = 0, gk = <<>>, gr = 0, bnd = 0;
begin
GC0: \* a pass: gc_watermark(): issued loaded as the bound, then min_active_ts's walk of the
     \* registry; or a watermark the embedder computes soundly
    if gr >= GcRounds then
        goto Done;
    elsif Watermark = "sound" then
        with w \in 1 .. SoundMax do wm := w; end with;
        gk := Ascending(Keys);
        gr := gr + 1;
        goto GC2;
    else
        bnd := issued || gThru := active || gEver := active;
    end if;
GC1: \* the walk ends: the watermark is the least value among the transactions it yielded, at
     \* most the bound (walk_only: the least alone, and no pass on an empty registry)
    with Y \in {Y \in SUBSET gEver : gThru \subseteq Y},
         w = IF MutWalkOnly THEN MinReg(Y) ELSE MinOpt(MinReg(Y), bnd) do
        gThru := {} || gEver := {} || bnd := 0;
        gr := gr + 1;
        if w = NONE then
            goto GC0;
        else
            wm := w || errs := errs \cup WmErr(w);
            gk := Ascending(Keys);
            goto GC2;
        end if;
    end with;
GC2: \* storage.gc_writes(key, watermark), or the key passed over
    with k = Head(gk) do
        either
            wr[k] := GcWrites(wr[k], wm);
            goto GC3;
        or
            if Len(gk) > 1 then gk := Tail(gk); goto GC2;
            else gk := <<>>; wm := 0; goto GC0;
            end if;
        end either;
    end with;
GC3: \* storage.gc_data(key, watermark)
    with k = Head(gk) do
        data[k] := GcData(data[k], wr[k], wm);
        if Len(gk) > 1 then gk := Tail(gk); goto GC2;
        else gk := <<>>; wm := 0; goto GC0;
        end if;
    end with;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "a7ab4876" /\ chksum(tla) = "51cdca64")
VARIABLES clock, hiTs, lock, wr, data, startTs, commitTs, readTs, cdone, 
          issued, regTs, active, gThru, gEver, inflight, epoch, hThru, hEver, 
          ssi, errs, pc

(* define statement *)
GcOn == Gc # {}
GcWalking == \E g \in Gc : pc[g] = "GC1"
HzWalking == \E x \in Hz : pc[x] = "HZ3"
TsErr(v) == IF v <= hiTs THEN {"ts"} ELSE {}


CommittedIn(k, r) ==
    {w \in AllTx : commitTs[w] # 0 /\ commitTs[w] <= r /\ FinalBuf[w][k] # "none"}
SnapVal(k, r) ==
    IF CommittedIn(k, r) = {} THEN NONE
    ELSE LET w == CHOOSE w \in CommittedIn(k, r) :
                      \A v \in CommittedIn(k, r) : commitTs[v] <= commitTs[w]
         IN IF FinalBuf[w][k] = "put" THEN w ELSE NONE

ReadErr(k, r, a) ==
    (IF a # SnapVal(k, r) THEN {"stale"} ELSE {})
        \cup (IF a # NONE /\ ~(commitTs[a] # 0 /\ commitTs[a] <= r) THEN {"dirty"} ELSE {})


SerErr(t) ==
    IF Iso(t) = "SER" /\ \E w \in Txns \ {t} :
           Iso(w) = "SER" /\ commitTs[w] > startTs[t] /\ RSet[t] \cap WSet[w] # {}
    THEN {"serial"} ELSE {}

ReadPhase == {"BG2", "OP", "XR1", "XR2", "RO", "RL", "RW", "RD"}
Live(t) == startTs[t] # 0 /\ pc[t] \in ReadPhase
NeedTs(t) ==
    IF Iso(t) = "RC" THEN (IF readTs[t] # 0 THEN readTs[t] ELSE clock + 1) ELSE startTs[t]
SoundMax == MinOf({NeedTs(t) : t \in {u \in Txns : Live(u)}} \cup {clock + 1})

WmErr(w) == IF \E t \in Txns : Live(t) /\ w > NeedTs(t) THEN {"watermark"} ELSE {}
MinStart(Y) == IF Y = {} THEN NONE ELSE MinOf({startTs[t] : t \in Y})
MinReg(Y) == IF Y = {} THEN NONE ELSE MinOf({regTs[t] : t \in Y})


HzErr(hv) ==
    IF \E w \in Txns : commitTs[w] # 0 /\ commitTs[w] <= hv /\ pc[w] # "Done"
    THEN {"horizon"} ELSE {}

VARIABLES i, todo, acq, left, rc, ck, ld, now, att, scans, cons, bef, mn, h, 
          rd, wm, gk, gr, bnd

vars == << clock, hiTs, lock, wr, data, startTs, commitTs, readTs, cdone, 
           issued, regTs, active, gThru, gEver, inflight, epoch, hThru, hEver, 
           ssi, errs, pc, i, todo, acq, left, rc, ck, ld, now, att, scans, 
           cons, bef, mn, h, rd, wm, gk, gr, bnd >>

ProcSet == (Txns) \cup (Hz) \cup (Gc)

Init == (* Global variables *)
        /\ clock = (IF Seeded = {} THEN 0 ELSE 2)
        /\ hiTs = (IF Seeded = {} THEN 0 ELSE 2)
        /\ lock = [k \in Keys |-> 0]
        /\ wr = [k \in Keys |-> IF k \in Seeded THEN {[ts |-> 2, st |-> 1, kind |-> "put"]} ELSE {}]
        /\ data = [k \in Keys |-> IF k \in Seeded THEN {[st |-> 1, val |-> 0]} ELSE {}]
        /\ startTs = [t \in AllTx |-> IF t = 0 THEN 1 ELSE 0]
        /\ commitTs = [t \in AllTx |-> IF t = 0 /\ Seeded # {} THEN 2 ELSE 0]
        /\ readTs = [t \in Txns |-> 0]
        /\ cdone = {}
        /\ issued = (IF Seeded = {} THEN 0 ELSE 2)
        /\ regTs = [t \in Txns |-> 0]
        /\ active = {}
        /\ gThru = {}
        /\ gEver = {}
        /\ inflight = {}
        /\ epoch = 0
        /\ hThru = {}
        /\ hEver = {}
        /\ ssi = 0
        /\ errs = {}
        (* Process Tx *)
        /\ i = [self \in Txns |-> 1]
        /\ todo = [self \in Txns |-> <<>>]
        /\ acq = [self \in Txns |-> <<>>]
        /\ left = [self \in Txns |-> {}]
        /\ rc = [self \in Txns |-> NoRec]
        /\ ck = [self \in Txns |-> 0]
        /\ ld = [self \in Txns |-> 0]
        (* Process Horizon *)
        /\ now = [self \in Hz |-> 0]
        /\ att = [self \in Hz |-> 0]
        /\ scans = [self \in Hz |-> 0]
        /\ cons = [self \in Hz |-> NONE]
        /\ bef = [self \in Hz |-> 0]
        /\ mn = [self \in Hz |-> NONE]
        /\ h = [self \in Hz |-> 0]
        /\ rd = [self \in Hz |-> 0]
        (* Process Collector *)
        /\ wm = [self \in Gc |-> 0]
        /\ gk = [self \in Gc |-> <<>>]
        /\ gr = [self \in Gc |-> 0]
        /\ bnd = [self \in Gc |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Txns -> "BG0"
                                        [] self \in Hz -> "HZ0"
                                        [] self \in Gc -> "GC0"]

BG0(self) == /\ pc[self] = "BG0"
             /\ IF GcOn /\ ~MutRegAfter
                   THEN /\ /\ active' = (active \cup {self})
                           /\ gEver' = (IF GcWalking THEN gEver \cup {self} ELSE gEver)
                           /\ regTs' = [regTs EXCEPT ![self] = issued]
                   ELSE /\ TRUE
                        /\ UNCHANGED << regTs, active, gEver >>
             /\ pc' = [pc EXCEPT ![self] = "BG1"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, gThru, inflight, epoch, 
                             hThru, hEver, ssi, errs, i, todo, acq, left, rc, 
                             ck, ld, now, att, scans, cons, bef, mn, h, rd, wm, 
                             gk, gr, bnd >>

BG1(self) == /\ pc[self] = "BG1"
             /\ IF MutOracle
                   THEN /\ ld' = [ld EXCEPT ![self] = clock]
                        /\ pc' = [pc EXCEPT ![self] = "BG1b"]
                        /\ UNCHANGED << clock, hiTs, startTs, issued, errs >>
                   ELSE /\ /\ clock' = clock + 1
                           /\ errs' = (errs \cup TsErr(clock + 1))
                           /\ hiTs' = Max2(hiTs, clock + 1)
                           /\ issued' = Max2(issued, clock + 1)
                           /\ startTs' = [startTs EXCEPT ![self] = clock + 1]
                        /\ IF GcOn
                              THEN /\ pc' = [pc EXCEPT ![self] = "BG2"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "OP"]
                        /\ ld' = ld
             /\ UNCHANGED << lock, wr, data, commitTs, readTs, cdone, regTs, 
                             active, gThru, gEver, inflight, epoch, hThru, 
                             hEver, ssi, i, todo, acq, left, rc, ck, now, att, 
                             scans, cons, bef, mn, h, rd, wm, gk, gr, bnd >>

BG1b(self) == /\ pc[self] = "BG1b"
              /\ /\ clock' = ld[self] + 1
                 /\ errs' = (errs \cup TsErr(ld[self] + 1))
                 /\ hiTs' = Max2(hiTs, ld[self] + 1)
                 /\ issued' = Max2(issued, ld[self] + 1)
                 /\ startTs' = [startTs EXCEPT ![self] = ld[self] + 1]
              /\ ld' = [ld EXCEPT ![self] = 0]
              /\ IF GcOn
                    THEN /\ pc' = [pc EXCEPT ![self] = "BG2"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "OP"]
              /\ UNCHANGED << lock, wr, data, commitTs, readTs, cdone, regTs, 
                              active, gThru, gEver, inflight, epoch, hThru, 
                              hEver, ssi, i, todo, acq, left, rc, ck, now, att, 
                              scans, cons, bef, mn, h, rd, wm, gk, gr, bnd >>

BG2(self) == /\ pc[self] = "BG2"
             /\ /\ active' = (active \cup {self})
                /\ gEver' = (IF GcWalking THEN gEver \cup {self} ELSE gEver)
                /\ regTs' = [regTs EXCEPT ![self] = startTs[self]]
             /\ pc' = [pc EXCEPT ![self] = "OP"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, gThru, inflight, epoch, 
                             hThru, hEver, ssi, errs, i, todo, acq, left, rc, 
                             ck, ld, now, att, scans, cons, bef, mn, h, rd, wm, 
                             gk, gr, bnd >>

OP(self) == /\ pc[self] = "OP"
            /\ LET j == NextT[self][i[self]] IN
                 /\ i' = [i EXCEPT ![self] = j]
                 /\ IF ExtApply /\ FirstW[self] # 0 /\ FirstW[self] < j /\ self \notin inflight
                       THEN /\ pc' = [pc EXCEPT ![self] = "XR1"]
                            /\ UNCHANGED << readTs, todo >>
                       ELSE /\ IF j <= NOps(self)
                                  THEN /\ IF Iso(self) = "RC"
                                             THEN /\ pc' = [pc EXCEPT ![self] = "RO"]
                                                  /\ UNCHANGED readTs
                                             ELSE /\ readTs' = [readTs EXCEPT ![self] = startTs[self]]
                                                  /\ pc' = [pc EXCEPT ![self] = "RL"]
                                       /\ todo' = todo
                                  ELSE /\ IF Plan[self].fin = "drop"
                                             THEN /\ IF GcOn /\ MutUnregFirst
                                                        THEN /\ pc' = [pc EXCEPT ![self] = "DR1"]
                                                        ELSE /\ IF self \in inflight
                                                                   THEN /\ pc' = [pc EXCEPT ![self] = "DR2"]
                                                                   ELSE /\ IF GcOn
                                                                              THEN /\ pc' = [pc EXCEPT ![self] = "DR1"]
                                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                  /\ todo' = todo
                                             ELSE /\ IF GcOn
                                                        THEN /\ pc' = [pc EXCEPT ![self] = "CM0"]
                                                             /\ todo' = todo
                                                        ELSE /\ IF WSet[self] = {}
                                                                   THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                                                                        /\ todo' = todo
                                                                   ELSE /\ IF MutCheckFirst
                                                                              THEN /\ todo' = [todo EXCEPT ![self] = Ascending(WSet[self])]
                                                                                   /\ pc' = [pc EXCEPT ![self] = "PC"]
                                                                              ELSE /\ todo' = [todo EXCEPT ![self] = Ascending(WSet[self])]
                                                                                   /\ pc' = [pc EXCEPT ![self] = "PL"]
                                       /\ UNCHANGED readTs
            /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                            cdone, issued, regTs, active, gThru, gEver, 
                            inflight, epoch, hThru, hEver, ssi, errs, acq, 
                            left, rc, ck, ld, now, att, scans, cons, bef, mn, 
                            h, rd, wm, gk, gr, bnd >>

XR1(self) == /\ pc[self] = "XR1"
             /\ IF MutNoEpoch
                   THEN /\ epoch' = epoch + 1
                        /\ UNCHANGED << inflight, hEver >>
                   ELSE /\ /\ hEver' = (IF HzWalking THEN hEver \cup {self} ELSE hEver)
                           /\ inflight' = (inflight \cup {self})
                        /\ epoch' = epoch
             /\ pc' = [pc EXCEPT ![self] = "XR2"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, hThru, ssi, errs, i, todo, acq, left, rc, 
                             ck, ld, now, att, scans, cons, bef, mn, h, rd, wm, 
                             gk, gr, bnd >>

XR2(self) == /\ pc[self] = "XR2"
             /\ IF MutNoEpoch
                   THEN /\ /\ hEver' = (IF HzWalking THEN hEver \cup {self} ELSE hEver)
                           /\ inflight' = (inflight \cup {self})
                        /\ epoch' = epoch
                   ELSE /\ epoch' = epoch + 1
                        /\ UNCHANGED << inflight, hEver >>
             /\ pc' = [pc EXCEPT ![self] = "OP"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, hThru, ssi, errs, i, todo, acq, left, rc, 
                             ck, ld, now, att, scans, cons, bef, mn, h, rd, wm, 
                             gk, gr, bnd >>

RO(self) == /\ pc[self] = "RO"
            /\ /\ clock' = clock + 1
               /\ errs' = (errs \cup TsErr(clock + 1))
               /\ hiTs' = Max2(hiTs, clock + 1)
               /\ issued' = Max2(issued, clock + 1)
               /\ readTs' = [readTs EXCEPT ![self] = clock + 1]
            /\ pc' = [pc EXCEPT ![self] = "RL"]
            /\ UNCHANGED << lock, wr, data, startTs, commitTs, cdone, regTs, 
                            active, gThru, gEver, inflight, epoch, hThru, 
                            hEver, ssi, i, todo, acq, left, rc, ck, ld, now, 
                            att, scans, cons, bef, mn, h, rd, wm, gk, gr, bnd >>

RL(self) == /\ pc[self] = "RL"
            /\ LET k == OpK(self, i[self]) IN
                 LET hd == lock[k] IN
                   IF hd # 0 /\ startTs[hd] <= readTs[self] /\ ~MutIgnoreLock
                      THEN /\ IF hd = self
                                 THEN /\ i' = [i EXCEPT ![self] = i[self] + 1]
                                      /\ readTs' = [readTs EXCEPT ![self] = 0]
                                      /\ pc' = [pc EXCEPT ![self] = "OP"]
                                      /\ errs' = errs
                                 ELSE /\ \/ /\ pc' = [pc EXCEPT ![self] = "RL"]
                                            /\ UNCHANGED <<readTs, errs, i>>
                                         \/ /\ ~MutReadWaits
                                            /\ errs' = (errs \cup (IF MutGiveUpNone /\ SnapVal(k, readTs[self]) # NONE
                                                                   THEN {"giveup"} ELSE {}))
                                            /\ i' = [i EXCEPT ![self] = i[self] + 1]
                                            /\ readTs' = [readTs EXCEPT ![self] = 0]
                                            /\ pc' = [pc EXCEPT ![self] = "OP"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "RW"]
                           /\ UNCHANGED << readTs, errs, i >>
            /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                            cdone, issued, regTs, active, gThru, gEver, 
                            inflight, epoch, hThru, hEver, ssi, todo, acq, 
                            left, rc, ck, ld, now, att, scans, cons, bef, mn, 
                            h, rd, wm, gk, gr, bnd >>

RW(self) == /\ pc[self] = "RW"
            /\ LET k == OpK(self, i[self]) IN
                 LET r == LatestCommit(wr[k], readTs[self]) IN
                   IF MutDataColumn
                      THEN /\ errs' = (errs \cup ReadErr(k, readTs[self], LatestData(data[k], readTs[self]).val))
                           /\ i' = [i EXCEPT ![self] = i[self] + 1]
                           /\ readTs' = [readTs EXCEPT ![self] = 0]
                           /\ pc' = [pc EXCEPT ![self] = "OP"]
                           /\ rc' = rc
                      ELSE /\ IF r.kind = "put"
                                 THEN /\ rc' = [rc EXCEPT ![self] = r]
                                      /\ pc' = [pc EXCEPT ![self] = "RD"]
                                      /\ UNCHANGED << readTs, errs, i >>
                                 ELSE /\ errs' = (errs \cup ReadErr(k, readTs[self], NONE))
                                      /\ i' = [i EXCEPT ![self] = i[self] + 1]
                                      /\ readTs' = [readTs EXCEPT ![self] = 0]
                                      /\ pc' = [pc EXCEPT ![self] = "OP"]
                                      /\ rc' = rc
            /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                            cdone, issued, regTs, active, gThru, gEver, 
                            inflight, epoch, hThru, hEver, ssi, todo, acq, 
                            left, ck, ld, now, att, scans, cons, bef, mn, h, 
                            rd, wm, gk, gr, bnd >>

RD(self) == /\ pc[self] = "RD"
            /\ LET k == OpK(self, i[self]) IN
                 LET v == DataAt(data[k], rc[self].st) IN
                   /\ IF v = NONE
                         THEN /\ errs' = (errs \cup (IF SnapVal(k, readTs[self]) # NONE THEN {"lost"} ELSE {}))
                         ELSE /\ errs' = (errs \cup ReadErr(k, readTs[self], v))
                   /\ i' = [i EXCEPT ![self] = i[self] + 1]
                   /\ readTs' = [readTs EXCEPT ![self] = 0]
                   /\ rc' = [rc EXCEPT ![self] = NoRec]
                   /\ pc' = [pc EXCEPT ![self] = "OP"]
            /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                            cdone, issued, regTs, active, gThru, gEver, 
                            inflight, epoch, hThru, hEver, ssi, todo, acq, 
                            left, ck, ld, now, att, scans, cons, bef, mn, h, 
                            rd, wm, gk, gr, bnd >>

DR1(self) == /\ pc[self] = "DR1"
             /\ /\ active' = active \ {self}
                /\ gThru' = gThru \ {self}
             /\ IF MutUnregFirst /\ self \in inflight
                   THEN /\ pc' = [pc EXCEPT ![self] = "DR2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, gEver, inflight, 
                             epoch, hThru, hEver, ssi, errs, i, todo, acq, 
                             left, rc, ck, ld, now, att, scans, cons, bef, mn, 
                             h, rd, wm, gk, gr, bnd >>

DR2(self) == /\ pc[self] = "DR2"
             /\ /\ hThru' = hThru \ {self}
                /\ inflight' = inflight \ {self}
             /\ IF GcOn /\ ~MutUnregFirst
                   THEN /\ pc' = [pc EXCEPT ![self] = "DR1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, epoch, hEver, ssi, errs, i, todo, acq, 
                             left, rc, ck, ld, now, att, scans, cons, bef, mn, 
                             h, rd, wm, gk, gr, bnd >>

CM0(self) == /\ pc[self] = "CM0"
             /\ IF MutUnregFirst
                   THEN /\ /\ active' = active \ {self}
                           /\ gThru' = gThru \ {self}
                   ELSE /\ TRUE
                        /\ UNCHANGED << active, gThru >>
             /\ IF WSet[self] = {}
                   THEN /\ pc' = [pc EXCEPT ![self] = "UR"]
                        /\ todo' = todo
                   ELSE /\ IF MutCheckFirst
                              THEN /\ todo' = [todo EXCEPT ![self] = Ascending(WSet[self])]
                                   /\ pc' = [pc EXCEPT ![self] = "PC"]
                              ELSE /\ todo' = [todo EXCEPT ![self] = Ascending(WSet[self])]
                                   /\ pc' = [pc EXCEPT ![self] = "PL"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, gEver, inflight, 
                             epoch, hThru, hEver, ssi, errs, i, acq, left, rc, 
                             ck, ld, now, att, scans, cons, bef, mn, h, rd, wm, 
                             gk, gr, bnd >>

PL(self) == /\ pc[self] = "PL"
            /\ LET k == Head(todo[self]) IN
                 IF lock[k] # 0 /\ lock[k] # self
                    THEN /\ todo' = [todo EXCEPT ![self] = <<>>]
                         /\ IF acq[self] # <<>>
                               THEN /\ pc' = [pc EXCEPT ![self] = "PF"]
                                    /\ acq' = acq
                               ELSE /\ acq' = [acq EXCEPT ![self] = <<>>]
                                    /\ IF self \in inflight
                                          THEN /\ pc' = [pc EXCEPT ![self] = "RBP"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "UR"]
                         /\ lock' = lock
                    ELSE /\ IF MutLockSplit
                               THEN /\ pc' = [pc EXCEPT ![self] = "PL2"]
                                    /\ UNCHANGED << lock, todo, acq >>
                               ELSE /\ lock' = [lock EXCEPT ![k] = self]
                                    /\ IF Len(todo[self]) > 1
                                          THEN /\ acq' = [acq EXCEPT ![self] = Append(acq[self], k)]
                                               /\ todo' = [todo EXCEPT ![self] = Tail(todo[self])]
                                               /\ pc' = [pc EXCEPT ![self] = "PL"]
                                          ELSE /\ IF ~MutCheckFirst
                                                     THEN /\ acq' = [acq EXCEPT ![self] = Append(acq[self], k)]
                                                          /\ todo' = [todo EXCEPT ![self] = Ascending(WSet[self])]
                                                          /\ pc' = [pc EXCEPT ![self] = "PC"]
                                                     ELSE /\ IF PutKeys(self) # {}
                                                                THEN /\ todo' = [todo EXCEPT ![self] = Ascending(PutKeys(self))]
                                                                     /\ acq' = [acq EXCEPT ![self] = <<>>]
                                                                     /\ pc' = [pc EXCEPT ![self] = "PD"]
                                                                ELSE /\ IF Iso(self) = "SER"
                                                                           THEN /\ todo' = [todo EXCEPT ![self] = <<>>]
                                                                                /\ acq' = [acq EXCEPT ![self] = <<>>]
                                                                                /\ pc' = [pc EXCEPT ![self] = "SL"]
                                                                           ELSE /\ todo' = [todo EXCEPT ![self] = <<>>]
                                                                                /\ acq' = [acq EXCEPT ![self] = <<>>]
                                                                                /\ pc' = [pc EXCEPT ![self] = "CT"]
            /\ UNCHANGED << clock, hiTs, wr, data, startTs, commitTs, readTs, 
                            cdone, issued, regTs, active, gThru, gEver, 
                            inflight, epoch, hThru, hEver, ssi, errs, i, left, 
                            rc, ck, ld, now, att, scans, cons, bef, mn, h, rd, 
                            wm, gk, gr, bnd >>

PL2(self) == /\ pc[self] = "PL2"
             /\ LET k == Head(todo[self]) IN
                  /\ lock' = [lock EXCEPT ![k] = self]
                  /\ acq' = [acq EXCEPT ![self] = Append(acq[self], k)]
                  /\ IF Len(todo[self]) > 1
                        THEN /\ todo' = [todo EXCEPT ![self] = Tail(todo[self])]
                             /\ pc' = [pc EXCEPT ![self] = "PL"]
                        ELSE /\ todo' = [todo EXCEPT ![self] = Ascending(WSet[self])]
                             /\ pc' = [pc EXCEPT ![self] = "PC"]
             /\ UNCHANGED << clock, hiTs, wr, data, startTs, commitTs, readTs, 
                             cdone, issued, regTs, active, gThru, gEver, 
                             inflight, epoch, hThru, hEver, ssi, errs, i, left, 
                             rc, ck, ld, now, att, scans, cons, bef, mn, h, rd, 
                             wm, gk, gr, bnd >>

PF(self) == /\ pc[self] = "PF"
            /\ lock' = [lock EXCEPT ![Head(acq[self])] = 0]
            /\ IF Len(acq[self]) > 1
                  THEN /\ acq' = [acq EXCEPT ![self] = Tail(acq[self])]
                       /\ pc' = [pc EXCEPT ![self] = "PF"]
                  ELSE /\ acq' = [acq EXCEPT ![self] = <<>>]
                       /\ IF self \in inflight
                             THEN /\ pc' = [pc EXCEPT ![self] = "RBP"]
                             ELSE /\ pc' = [pc EXCEPT ![self] = "UR"]
            /\ UNCHANGED << clock, hiTs, wr, data, startTs, commitTs, readTs, 
                            cdone, issued, regTs, active, gThru, gEver, 
                            inflight, epoch, hThru, hEver, ssi, errs, i, todo, 
                            left, rc, ck, ld, now, att, scans, cons, bef, mn, 
                            h, rd, wm, gk, gr, bnd >>

RBP(self) == /\ pc[self] = "RBP"
             /\ /\ hThru' = hThru \ {self}
                /\ inflight' = inflight \ {self}
             /\ pc' = [pc EXCEPT ![self] = "UR"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, epoch, hEver, ssi, errs, i, todo, acq, 
                             left, rc, ck, ld, now, att, scans, cons, bef, mn, 
                             h, rd, wm, gk, gr, bnd >>

PC(self) == /\ pc[self] = "PC"
            /\ LET k == Head(todo[self]) IN
                 LET r == LatestWrite(wr[k], INF) IN
                   IF r.kind # "none" /\ r.ts >= startTs[self] /\ (r.kind = "rb" \/ ~MutSkipNewer)
                      THEN /\ todo' = [todo EXCEPT ![self] = <<>>]
                           /\ IF acq[self] # <<>>
                                 THEN /\ pc' = [pc EXCEPT ![self] = "PF"]
                                      /\ acq' = acq
                                 ELSE /\ acq' = [acq EXCEPT ![self] = <<>>]
                                      /\ IF self \in inflight
                                            THEN /\ pc' = [pc EXCEPT ![self] = "RBP"]
                                            ELSE /\ pc' = [pc EXCEPT ![self] = "UR"]
                      ELSE /\ IF Len(todo[self]) > 1
                                 THEN /\ todo' = [todo EXCEPT ![self] = Tail(todo[self])]
                                      /\ pc' = [pc EXCEPT ![self] = "PC"]
                                      /\ acq' = acq
                                 ELSE /\ IF MutCheckFirst
                                            THEN /\ todo' = [todo EXCEPT ![self] = Ascending(WSet[self])]
                                                 /\ pc' = [pc EXCEPT ![self] = "PL"]
                                                 /\ acq' = acq
                                            ELSE /\ IF PutKeys(self) # {}
                                                       THEN /\ todo' = [todo EXCEPT ![self] = Ascending(PutKeys(self))]
                                                            /\ acq' = [acq EXCEPT ![self] = <<>>]
                                                            /\ pc' = [pc EXCEPT ![self] = "PD"]
                                                       ELSE /\ IF Iso(self) = "SER" /\ ~MutLateCheck
                                                                  THEN /\ todo' = [todo EXCEPT ![self] = <<>>]
                                                                       /\ acq' = [acq EXCEPT ![self] = <<>>]
                                                                       /\ pc' = [pc EXCEPT ![self] = "SL"]
                                                                  ELSE /\ todo' = [todo EXCEPT ![self] = <<>>]
                                                                       /\ acq' = [acq EXCEPT ![self] = <<>>]
                                                                       /\ pc' = [pc EXCEPT ![self] = "CT"]
            /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                            readTs, cdone, issued, regTs, active, gThru, gEver, 
                            inflight, epoch, hThru, hEver, ssi, errs, i, left, 
                            rc, ck, ld, now, att, scans, cons, bef, mn, h, rd, 
                            wm, gk, gr, bnd >>

PD(self) == /\ pc[self] = "PD"
            /\ LET k == Head(todo[self]) IN
                 /\ data' = [data EXCEPT ![k] = PutData(data[k], startTs[self], self)]
                 /\ IF Len(todo[self]) > 1
                       THEN /\ todo' = [todo EXCEPT ![self] = Tail(todo[self])]
                            /\ pc' = [pc EXCEPT ![self] = "PD"]
                       ELSE /\ IF Iso(self) = "SER" /\ ~MutLateCheck
                                  THEN /\ todo' = [todo EXCEPT ![self] = <<>>]
                                       /\ pc' = [pc EXCEPT ![self] = "SL"]
                                  ELSE /\ todo' = [todo EXCEPT ![self] = <<>>]
                                       /\ pc' = [pc EXCEPT ![self] = "CT"]
            /\ UNCHANGED << clock, hiTs, lock, wr, startTs, commitTs, readTs, 
                            cdone, issued, regTs, active, gThru, gEver, 
                            inflight, epoch, hThru, hEver, ssi, errs, i, acq, 
                            left, rc, ck, ld, now, att, scans, cons, bef, mn, 
                            h, rd, wm, gk, gr, bnd >>

SL(self) == /\ pc[self] = "SL"
            /\ ssi = 0 \/ MutNoSsiLock
            /\ IF ~MutNoSsiLock
                  THEN /\ ssi' = self
                  ELSE /\ TRUE
                       /\ ssi' = ssi
            /\ IF RSet[self] # {}
                  THEN /\ left' = [left EXCEPT ![self] = RSet[self]]
                       /\ pc' = [pc EXCEPT ![self] = "SV"]
                  ELSE /\ IF ~MutLateCheck
                             THEN /\ pc' = [pc EXCEPT ![self] = "CT"]
                                  /\ left' = left
                             ELSE /\ IF WSet[self] \ {Primary[self]} # {}
                                        THEN /\ left' = [left EXCEPT ![self] = WSet[self] \ {Primary[self]}]
                                             /\ pc' = [pc EXCEPT ![self] = "CS1"]
                                        ELSE /\ IF ssi' = self
                                                   THEN /\ pc' = [pc EXCEPT ![self] = "CE"]
                                                   ELSE /\ IF ExtApply
                                                              THEN /\ pc' = [pc EXCEPT ![self] = "URX"]
                                                              ELSE /\ pc' = [pc EXCEPT ![self] = "UR"]
                                             /\ left' = left
            /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                            readTs, cdone, issued, regTs, active, gThru, gEver, 
                            inflight, epoch, hThru, hEver, errs, i, todo, acq, 
                            rc, ck, ld, now, att, scans, cons, bef, mn, h, rd, 
                            wm, gk, gr, bnd >>

SV(self) == /\ pc[self] = "SV"
            /\ \E k \in left[self]:
                 LET r == IF MutSsiRecord THEN LatestWrite(wr[k], INF) ELSE LatestCommit(wr[k], INF) IN
                   IF r.kind \in {"put", "del"} /\ r.ts > startTs[self]
                      THEN /\ IF ExtApply
                                 THEN /\ left' = [left EXCEPT ![self] = {}]
                                      /\ pc' = [pc EXCEPT ![self] = "RB0"]
                                 ELSE /\ left' = [left EXCEPT ![self] = WSet[self]]
                                      /\ pc' = [pc EXCEPT ![self] = "RB1"]
                      ELSE /\ IF left[self] # {k}
                                 THEN /\ left' = [left EXCEPT ![self] = left[self] \ {k}]
                                      /\ pc' = [pc EXCEPT ![self] = "SV"]
                                 ELSE /\ IF ~MutLateCheck
                                            THEN /\ left' = [left EXCEPT ![self] = {}]
                                                 /\ pc' = [pc EXCEPT ![self] = "CT"]
                                            ELSE /\ IF WSet[self] \ {Primary[self]} # {}
                                                       THEN /\ left' = [left EXCEPT ![self] = WSet[self] \ {Primary[self]}]
                                                            /\ pc' = [pc EXCEPT ![self] = "CS1"]
                                                       ELSE /\ IF ssi = self
                                                                  THEN /\ left' = [left EXCEPT ![self] = {}]
                                                                       /\ pc' = [pc EXCEPT ![self] = "CE"]
                                                                  ELSE /\ IF ExtApply
                                                                             THEN /\ left' = [left EXCEPT ![self] = {}]
                                                                                  /\ pc' = [pc EXCEPT ![self] = "URX"]
                                                                             ELSE /\ left' = [left EXCEPT ![self] = {}]
                                                                                  /\ pc' = [pc EXCEPT ![self] = "UR"]
            /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                            readTs, cdone, issued, regTs, active, gThru, gEver, 
                            inflight, epoch, hThru, hEver, ssi, errs, i, todo, 
                            acq, rc, ck, ld, now, att, scans, cons, bef, mn, h, 
                            rd, wm, gk, gr, bnd >>

CT(self) == /\ pc[self] = "CT"
            /\ /\ clock' = clock + 1
               /\ commitTs' = [commitTs EXCEPT ![self] = clock + 1]
               /\ errs' = (errs \cup TsErr(clock + 1) \cup SerErr(self))
               /\ hiTs' = Max2(hiTs, clock + 1)
               /\ issued' = Max2(issued, clock + 1)
            /\ IF MutSecFirst /\ WSet[self] \ {Primary[self]} # {}
                  THEN /\ left' = [left EXCEPT ![self] = WSet[self] \ {Primary[self]}]
                       /\ pc' = [pc EXCEPT ![self] = "CS1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "CP1"]
                       /\ left' = left
            /\ UNCHANGED << lock, wr, data, startTs, readTs, cdone, regTs, 
                            active, gThru, gEver, inflight, epoch, hThru, 
                            hEver, ssi, i, todo, acq, rc, ck, ld, now, att, 
                            scans, cons, bef, mn, h, rd, wm, gk, gr, bnd >>

CP1(self) == /\ pc[self] = "CP1"
             /\ IF lock[Primary[self]] # self
                   THEN /\ errs' = (errs \cup {"primary"})
                        /\ IF ExtApply
                              THEN /\ pc' = [pc EXCEPT ![self] = "RB0"]
                                   /\ left' = left
                              ELSE /\ left' = [left EXCEPT ![self] = WSet[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "RB1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "CP2"]
                        /\ UNCHANGED << errs, left >>
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, inflight, epoch, hThru, hEver, ssi, i, 
                             todo, acq, rc, ck, ld, now, att, scans, cons, bef, 
                             mn, h, rd, wm, gk, gr, bnd >>

CP2(self) == /\ pc[self] = "CP2"
             /\ /\ cdone' = (cdone \cup {self})
                /\ wr' = [wr EXCEPT ![Primary[self]] = PutRec(wr[Primary[self]],
                                                              [ts |-> commitTs[self], st |-> startTs[self],
                                                               kind |-> FinalBuf[self][Primary[self]]])]
             /\ pc' = [pc EXCEPT ![self] = "CP3"]
             /\ UNCHANGED << clock, hiTs, lock, data, startTs, commitTs, 
                             readTs, issued, regTs, active, gThru, gEver, 
                             inflight, epoch, hThru, hEver, ssi, errs, i, todo, 
                             acq, left, rc, ck, ld, now, att, scans, cons, bef, 
                             mn, h, rd, wm, gk, gr, bnd >>

CP3(self) == /\ pc[self] = "CP3"
             /\ lock' = [lock EXCEPT ![Primary[self]] = 0]
             /\ IF Iso(self) = "SER" /\ MutLateCheck
                   THEN /\ pc' = [pc EXCEPT ![self] = "SL"]
                        /\ left' = left
                   ELSE /\ IF ~MutSecFirst /\ WSet[self] \ {Primary[self]} # {}
                              THEN /\ left' = [left EXCEPT ![self] = WSet[self] \ {Primary[self]}]
                                   /\ pc' = [pc EXCEPT ![self] = "CS1"]
                              ELSE /\ IF ssi = self \/ (MutExtUnreg /\ self \in inflight)
                                         THEN /\ pc' = [pc EXCEPT ![self] = "CE"]
                                         ELSE /\ IF ExtApply
                                                    THEN /\ pc' = [pc EXCEPT ![self] = "URX"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "UR"]
                                   /\ left' = left
             /\ UNCHANGED << clock, hiTs, wr, data, startTs, commitTs, readTs, 
                             cdone, issued, regTs, active, gThru, gEver, 
                             inflight, epoch, hThru, hEver, ssi, errs, i, todo, 
                             acq, rc, ck, ld, now, att, scans, cons, bef, mn, 
                             h, rd, wm, gk, gr, bnd >>

CS1(self) == /\ pc[self] = "CS1"
             /\ \E k \in left[self]:
                  /\ wr' = [wr EXCEPT ![k] = PutRec(wr[k], [ts |-> commitTs[self], st |-> startTs[self],
                                                            kind |-> FinalBuf[self][k]])]
                  /\ ck' = [ck EXCEPT ![self] = k]
             /\ pc' = [pc EXCEPT ![self] = "CS2"]
             /\ UNCHANGED << clock, hiTs, lock, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, inflight, epoch, hThru, hEver, ssi, errs, 
                             i, todo, acq, left, rc, ld, now, att, scans, cons, 
                             bef, mn, h, rd, wm, gk, gr, bnd >>

CS2(self) == /\ pc[self] = "CS2"
             /\ IF lock[ck[self]] = self /\ ~MutSecKeepsLock
                   THEN /\ pc' = [pc EXCEPT ![self] = "CS3"]
                        /\ UNCHANGED << left, ck >>
                   ELSE /\ left' = [left EXCEPT ![self] = left[self] \ {ck[self]}]
                        /\ ck' = [ck EXCEPT ![self] = 0]
                        /\ IF left'[self] # {}
                              THEN /\ pc' = [pc EXCEPT ![self] = "CS1"]
                              ELSE /\ IF MutSecFirst
                                         THEN /\ pc' = [pc EXCEPT ![self] = "CP1"]
                                         ELSE /\ IF ssi = self \/ (MutExtUnreg /\ self \in inflight)
                                                    THEN /\ pc' = [pc EXCEPT ![self] = "CE"]
                                                    ELSE /\ IF ExtApply
                                                               THEN /\ pc' = [pc EXCEPT ![self] = "URX"]
                                                               ELSE /\ pc' = [pc EXCEPT ![self] = "UR"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, inflight, epoch, hThru, hEver, ssi, errs, 
                             i, todo, acq, rc, ld, now, att, scans, cons, bef, 
                             mn, h, rd, wm, gk, gr, bnd >>

CS3(self) == /\ pc[self] = "CS3"
             /\ lock' = [lock EXCEPT ![ck[self]] = 0]
             /\ left' = [left EXCEPT ![self] = left[self] \ {ck[self]}]
             /\ ck' = [ck EXCEPT ![self] = 0]
             /\ IF left'[self] # {}
                   THEN /\ pc' = [pc EXCEPT ![self] = "CS1"]
                   ELSE /\ IF MutSecFirst
                              THEN /\ pc' = [pc EXCEPT ![self] = "CP1"]
                              ELSE /\ IF ssi = self \/ (MutExtUnreg /\ self \in inflight)
                                         THEN /\ pc' = [pc EXCEPT ![self] = "CE"]
                                         ELSE /\ IF ExtApply
                                                    THEN /\ pc' = [pc EXCEPT ![self] = "URX"]
                                                    ELSE /\ pc' = [pc EXCEPT ![self] = "UR"]
             /\ UNCHANGED << clock, hiTs, wr, data, startTs, commitTs, readTs, 
                             cdone, issued, regTs, active, gThru, gEver, 
                             inflight, epoch, hThru, hEver, ssi, errs, i, todo, 
                             acq, rc, ld, now, att, scans, cons, bef, mn, h, 
                             rd, wm, gk, gr, bnd >>

CE(self) == /\ pc[self] = "CE"
            /\ IF ssi = self
                  THEN /\ ssi' = 0
                  ELSE /\ TRUE
                       /\ ssi' = ssi
            /\ IF MutExtUnreg
                  THEN /\ /\ hThru' = hThru \ {self}
                          /\ inflight' = inflight \ {self}
                  ELSE /\ TRUE
                       /\ UNCHANGED << inflight, hThru >>
            /\ IF ExtApply /\ self \in cdone
                  THEN /\ pc' = [pc EXCEPT ![self] = "URX"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "UR"]
            /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                            readTs, cdone, issued, regTs, active, gThru, gEver, 
                            epoch, hEver, errs, i, todo, acq, left, rc, ck, ld, 
                            now, att, scans, cons, bef, mn, h, rd, wm, gk, gr, 
                            bnd >>

XA(self) == /\ pc[self] = "XA"
            /\ /\ hThru' = hThru \ {self}
               /\ inflight' = inflight \ {self}
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                            readTs, cdone, issued, regTs, active, gThru, gEver, 
                            epoch, hEver, ssi, errs, i, todo, acq, left, rc, 
                            ck, ld, now, att, scans, cons, bef, mn, h, rd, wm, 
                            gk, gr, bnd >>

UR(self) == /\ pc[self] = "UR"
            /\ IF ~MutUnregFirst
                  THEN /\ /\ active' = active \ {self}
                          /\ gThru' = gThru \ {self}
                  ELSE /\ TRUE
                       /\ UNCHANGED << active, gThru >>
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                            readTs, cdone, issued, regTs, gEver, inflight, 
                            epoch, hThru, hEver, ssi, errs, i, todo, acq, left, 
                            rc, ck, ld, now, att, scans, cons, bef, mn, h, rd, 
                            wm, gk, gr, bnd >>

URX(self) == /\ pc[self] = "URX"
             /\ IF ~MutUnregFirst
                   THEN /\ /\ active' = active \ {self}
                           /\ gThru' = gThru \ {self}
                   ELSE /\ TRUE
                        /\ UNCHANGED << active, gThru >>
             /\ pc' = [pc EXCEPT ![self] = "XA"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, gEver, inflight, 
                             epoch, hThru, hEver, ssi, errs, i, todo, acq, 
                             left, rc, ck, ld, now, att, scans, cons, bef, mn, 
                             h, rd, wm, gk, gr, bnd >>

RB0(self) == /\ pc[self] = "RB0"
             /\ /\ hThru' = hThru \ {self}
                /\ inflight' = inflight \ {self}
             /\ left' = [left EXCEPT ![self] = WSet[self]]
             /\ pc' = [pc EXCEPT ![self] = "RB1"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, epoch, hEver, ssi, errs, i, todo, acq, rc, 
                             ck, ld, now, att, scans, cons, bef, mn, h, rd, wm, 
                             gk, gr, bnd >>

RB1(self) == /\ pc[self] = "RB1"
             /\ \E k \in left[self]:
                  IF lock[k] = self
                     THEN /\ ck' = [ck EXCEPT ![self] = k]
                          /\ pc' = [pc EXCEPT ![self] = "RB2"]
                          /\ left' = left
                     ELSE /\ left' = [left EXCEPT ![self] = left[self] \ {k}]
                          /\ IF left'[self] # {}
                                THEN /\ pc' = [pc EXCEPT ![self] = "RB1"]
                                ELSE /\ IF ssi = self /\ ~MutKeepSsi
                                           THEN /\ pc' = [pc EXCEPT ![self] = "CE"]
                                           ELSE /\ pc' = [pc EXCEPT ![self] = "UR"]
                          /\ ck' = ck
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, inflight, epoch, hThru, hEver, ssi, errs, 
                             i, todo, acq, rc, ld, now, att, scans, cons, bef, 
                             mn, h, rd, wm, gk, gr, bnd >>

RB2(self) == /\ pc[self] = "RB2"
             /\ lock' = [lock EXCEPT ![ck[self]] = 0]
             /\ IF MutKeepData
                   THEN /\ pc' = [pc EXCEPT ![self] = "RB4"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "RB3"]
             /\ UNCHANGED << clock, hiTs, wr, data, startTs, commitTs, readTs, 
                             cdone, issued, regTs, active, gThru, gEver, 
                             inflight, epoch, hThru, hEver, ssi, errs, i, todo, 
                             acq, left, rc, ck, ld, now, att, scans, cons, bef, 
                             mn, h, rd, wm, gk, gr, bnd >>

RB3(self) == /\ pc[self] = "RB3"
             /\ data' = [data EXCEPT ![ck[self]] = IF MutRange THEN {d \in data[ck[self]] : d.st > startTs[self]}
                                                   ELSE {d \in data[ck[self]] : d.st # startTs[self]}]
             /\ pc' = [pc EXCEPT ![self] = "RB4"]
             /\ UNCHANGED << clock, hiTs, lock, wr, startTs, commitTs, readTs, 
                             cdone, issued, regTs, active, gThru, gEver, 
                             inflight, epoch, hThru, hEver, ssi, errs, i, todo, 
                             acq, left, rc, ck, ld, now, att, scans, cons, bef, 
                             mn, h, rd, wm, gk, gr, bnd >>

RB4(self) == /\ pc[self] = "RB4"
             /\ wr' = [wr EXCEPT ![ck[self]] = PutRec(wr[ck[self]], [ts |-> startTs[self], st |-> startTs[self], kind |-> "rb"])]
             /\ left' = [left EXCEPT ![self] = left[self] \ {ck[self]}]
             /\ ck' = [ck EXCEPT ![self] = 0]
             /\ IF left'[self] # {}
                   THEN /\ pc' = [pc EXCEPT ![self] = "RB1"]
                   ELSE /\ IF ssi = self /\ ~MutKeepSsi
                              THEN /\ pc' = [pc EXCEPT ![self] = "CE"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "UR"]
             /\ UNCHANGED << clock, hiTs, lock, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, inflight, epoch, hThru, hEver, ssi, errs, 
                             i, todo, acq, rc, ld, now, att, scans, cons, bef, 
                             mn, h, rd, wm, gk, gr, bnd >>

Tx(self) == BG0(self) \/ BG1(self) \/ BG1b(self) \/ BG2(self) \/ OP(self)
               \/ XR1(self) \/ XR2(self) \/ RO(self) \/ RL(self)
               \/ RW(self) \/ RD(self) \/ DR1(self) \/ DR2(self)
               \/ CM0(self) \/ PL(self) \/ PL2(self) \/ PF(self)
               \/ RBP(self) \/ PC(self) \/ PD(self) \/ SL(self) \/ SV(self)
               \/ CT(self) \/ CP1(self) \/ CP2(self) \/ CP3(self)
               \/ CS1(self) \/ CS2(self) \/ CS3(self) \/ CE(self)
               \/ XA(self) \/ UR(self) \/ URX(self) \/ RB0(self)
               \/ RB1(self) \/ RB2(self) \/ RB3(self) \/ RB4(self)

HZ0(self) == /\ pc[self] = "HZ0"
             /\ IF rd[self] >= HzRounds
                   THEN /\ now' = [now EXCEPT ![self] = 0]
                        /\ att' = [att EXCEPT ![self] = 0]
                        /\ h' = [h EXCEPT ![self] = 0]
                        /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << clock, hiTs, errs, rd >>
                   ELSE /\ /\ clock' = clock + 1
                           /\ errs' = (errs \cup TsErr(clock + 1))
                           /\ hiTs' = Max2(hiTs, clock + 1)
                           /\ now' = [now EXCEPT ![self] = clock + 1]
                        /\ att' = [att EXCEPT ![self] = 0]
                        /\ h' = [h EXCEPT ![self] = 0]
                        /\ rd' = [rd EXCEPT ![self] = rd[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "HZ1"]
             /\ UNCHANGED << lock, wr, data, startTs, commitTs, readTs, cdone, 
                             issued, regTs, active, gThru, gEver, inflight, 
                             epoch, hThru, hEver, ssi, i, todo, acq, left, rc, 
                             ck, ld, scans, cons, bef, mn, wm, gk, gr, bnd >>

HZ1(self) == /\ pc[self] = "HZ1"
             /\ bef' = [bef EXCEPT ![self] = epoch]
             /\ pc' = [pc EXCEPT ![self] = "HZ2"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, inflight, epoch, hThru, hEver, ssi, errs, 
                             i, todo, acq, left, rc, ck, ld, now, att, scans, 
                             cons, mn, h, rd, wm, gk, gr, bnd >>

HZ2(self) == /\ pc[self] = "HZ2"
             /\ /\ hEver' = inflight
                /\ hThru' = inflight
             /\ pc' = [pc EXCEPT ![self] = "HZ3"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, inflight, epoch, ssi, errs, i, todo, acq, 
                             left, rc, ck, ld, now, att, scans, cons, bef, mn, 
                             h, rd, wm, gk, gr, bnd >>

HZ3(self) == /\ pc[self] = "HZ3"
             /\ \E Y \in {Y \in SUBSET hEver : hThru \subseteq Y}:
                  mn' = [mn EXCEPT ![self] = MinStart(Y)]
             /\ /\ hEver' = {}
                /\ hThru' = {}
             /\ pc' = [pc EXCEPT ![self] = "HZ4"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, inflight, epoch, ssi, errs, i, todo, acq, 
                             left, rc, ck, ld, now, att, scans, cons, bef, h, 
                             rd, wm, gk, gr, bnd >>

HZ4(self) == /\ pc[self] = "HZ4"
             /\ IF epoch # bef[self] /\ ~MutNoEpoch /\ scans[self] + 1 < ScanRetries
                   THEN /\ /\ bef' = [bef EXCEPT ![self] = 0]
                           /\ cons' = [cons EXCEPT ![self] = MinOpt(cons[self], mn[self])]
                           /\ mn' = [mn EXCEPT ![self] = NONE]
                           /\ scans' = [scans EXCEPT ![self] = scans[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "HZ1"]
                        /\ UNCHANGED << errs, att, h >>
                   ELSE /\ LET m == IF epoch = bef[self] \/ MutNoEpoch THEN mn[self] ELSE MinOpt(cons[self], mn[self]) IN
                             /\ /\ bef' = [bef EXCEPT ![self] = 0]
                                /\ cons' = [cons EXCEPT ![self] = NONE]
                                /\ mn' = [mn EXCEPT ![self] = NONE]
                                /\ scans' = [scans EXCEPT ![self] = 0]
                             /\ IF m = NONE \/ m > now[self]
                                   THEN /\ /\ errs' = (errs \cup HzErr(now[self]))
                                           /\ h' = [h EXCEPT ![self] = now[self]]
                                        /\ pc' = [pc EXCEPT ![self] = "HZ0"]
                                        /\ att' = att
                                   ELSE /\ IF att[self] >= SpinCap /\ ~MutSpinForever
                                              THEN /\ LET hv == IF MutCapNow THEN now[self] ELSE Min2(now[self], Max2(m - 1, 0)) IN
                                                        /\ errs' = (errs \cup HzErr(hv))
                                                        /\ h' = [h EXCEPT ![self] = hv]
                                                   /\ pc' = [pc EXCEPT ![self] = "HZ0"]
                                                   /\ att' = att
                                              ELSE /\ att' = [att EXCEPT ![self] = IF MutSpinForever THEN att[self] ELSE att[self] + 1]
                                                   /\ pc' = [pc EXCEPT ![self] = "HZ1"]
                                                   /\ UNCHANGED << errs, h >>
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, inflight, epoch, hThru, hEver, ssi, i, 
                             todo, acq, left, rc, ck, ld, now, rd, wm, gk, gr, 
                             bnd >>

Horizon(self) == HZ0(self) \/ HZ1(self) \/ HZ2(self) \/ HZ3(self)
                    \/ HZ4(self)

GC0(self) == /\ pc[self] = "GC0"
             /\ IF gr[self] >= GcRounds
                   THEN /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << gThru, gEver, wm, gk, gr, bnd >>
                   ELSE /\ IF Watermark = "sound"
                              THEN /\ \E w \in 1 .. SoundMax:
                                        wm' = [wm EXCEPT ![self] = w]
                                   /\ gk' = [gk EXCEPT ![self] = Ascending(Keys)]
                                   /\ gr' = [gr EXCEPT ![self] = gr[self] + 1]
                                   /\ pc' = [pc EXCEPT ![self] = "GC2"]
                                   /\ UNCHANGED << gThru, gEver, bnd >>
                              ELSE /\ /\ bnd' = [bnd EXCEPT ![self] = issued]
                                      /\ gEver' = active
                                      /\ gThru' = active
                                   /\ pc' = [pc EXCEPT ![self] = "GC1"]
                                   /\ UNCHANGED << wm, gk, gr >>
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, inflight, 
                             epoch, hThru, hEver, ssi, errs, i, todo, acq, 
                             left, rc, ck, ld, now, att, scans, cons, bef, mn, 
                             h, rd >>

GC1(self) == /\ pc[self] = "GC1"
             /\ \E Y \in {Y \in SUBSET gEver : gThru \subseteq Y}:
                  LET w == IF MutWalkOnly THEN MinReg(Y) ELSE MinOpt(MinReg(Y), bnd[self]) IN
                    /\ /\ bnd' = [bnd EXCEPT ![self] = 0]
                       /\ gEver' = {}
                       /\ gThru' = {}
                    /\ gr' = [gr EXCEPT ![self] = gr[self] + 1]
                    /\ IF w = NONE
                          THEN /\ pc' = [pc EXCEPT ![self] = "GC0"]
                               /\ UNCHANGED << errs, wm, gk >>
                          ELSE /\ /\ errs' = (errs \cup WmErr(w))
                                  /\ wm' = [wm EXCEPT ![self] = w]
                               /\ gk' = [gk EXCEPT ![self] = Ascending(Keys)]
                               /\ pc' = [pc EXCEPT ![self] = "GC2"]
             /\ UNCHANGED << clock, hiTs, lock, wr, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, inflight, 
                             epoch, hThru, hEver, ssi, i, todo, acq, left, rc, 
                             ck, ld, now, att, scans, cons, bef, mn, h, rd >>

GC2(self) == /\ pc[self] = "GC2"
             /\ LET k == Head(gk[self]) IN
                  \/ /\ wr' = [wr EXCEPT ![k] = GcWrites(wr[k], wm[self])]
                     /\ pc' = [pc EXCEPT ![self] = "GC3"]
                     /\ UNCHANGED <<wm, gk>>
                  \/ /\ IF Len(gk[self]) > 1
                           THEN /\ gk' = [gk EXCEPT ![self] = Tail(gk[self])]
                                /\ pc' = [pc EXCEPT ![self] = "GC2"]
                                /\ wm' = wm
                           ELSE /\ gk' = [gk EXCEPT ![self] = <<>>]
                                /\ wm' = [wm EXCEPT ![self] = 0]
                                /\ pc' = [pc EXCEPT ![self] = "GC0"]
                     /\ wr' = wr
             /\ UNCHANGED << clock, hiTs, lock, data, startTs, commitTs, 
                             readTs, cdone, issued, regTs, active, gThru, 
                             gEver, inflight, epoch, hThru, hEver, ssi, errs, 
                             i, todo, acq, left, rc, ck, ld, now, att, scans, 
                             cons, bef, mn, h, rd, gr, bnd >>

GC3(self) == /\ pc[self] = "GC3"
             /\ LET k == Head(gk[self]) IN
                  /\ data' = [data EXCEPT ![k] = GcData(data[k], wr[k], wm[self])]
                  /\ IF Len(gk[self]) > 1
                        THEN /\ gk' = [gk EXCEPT ![self] = Tail(gk[self])]
                             /\ pc' = [pc EXCEPT ![self] = "GC2"]
                             /\ wm' = wm
                        ELSE /\ gk' = [gk EXCEPT ![self] = <<>>]
                             /\ wm' = [wm EXCEPT ![self] = 0]
                             /\ pc' = [pc EXCEPT ![self] = "GC0"]
             /\ UNCHANGED << clock, hiTs, lock, wr, startTs, commitTs, readTs, 
                             cdone, issued, regTs, active, gThru, gEver, 
                             inflight, epoch, hThru, hEver, ssi, errs, i, todo, 
                             acq, left, rc, ck, ld, now, att, scans, cons, bef, 
                             mn, h, rd, gr, bnd >>

Collector(self) == GC0(self) \/ GC1(self) \/ GC2(self) \/ GC3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Txns: Tx(self))
           \/ (\E self \in Hz: Horizon(self))
           \/ (\E self \in Gc: Collector(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
