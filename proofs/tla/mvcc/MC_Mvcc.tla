------------------------------- MODULE MC_Mvcc -------------------------------
(***************************************************************************)
(* The properties checked of Mvcc.tla, the fair specification, the          *)
(* witnesses, and the configurations' programs: each transaction's          *)
(* isolation level, its operations in order, and its end.                   *)
(***************************************************************************)
EXTENDS Mvcc

AllDone == \A p \in ProcSet : pc[p] = "Done"
HasCommitRec(k, w) == \E r \in wr[k] : r.st = startTs[w] /\ r.kind \in {"put", "del"}

\* Every timestamp the oracle hands out is greater than every one it handed out before: unique,
\* and increasing in the order they are handed out.
TsIncreasing == "ts" \notin errs
\* A read that answers from the version chain answers the value of the latest version committed
\* at or before its read timestamp (start_ts, or ReadCommitted's fresh one); None when that
\* version is a Delete or there is none.
SnapshotRead == "stale" \notin errs
\* No read answers a value whose transaction had not committed at or before its timestamp.
NoDirtyRead == "dirty" \notin errs
\* The version a read finds still has its data.
VersionData == "lost" \notin errs
\* A read that gives up after backing off answers no value: Err(LockConflict), never a None the
\* snapshot may contradict.
GiveUpSound == "giveup" \notin errs
\* A Serializable transaction that takes its commit_ts read no key that another Serializable
\* transaction committed after its start_ts.
SerialReads == "serial" \notin errs
\* A garbage collector's watermark from gc_watermark is at or below every timestamp a live
\* transaction reads at.
WatermarkSound == "watermark" \notin errs
\* safe_read_ts never answers a horizon at or above the commit_ts of a writer whose external
\* apply has not finished.
SafeReadTs == "horizon" \notin errs

\* commit_primary always finds the primary's lock its own: PrimaryLockMissing and
\* PrimaryLockMismatch are never answered.
PrimaryHeld == "primary" \notin errs

\* Two transactions that overlap in time ([start_ts, commit_ts]) and write a common key do not
\* both commit.
FirstCommitterWins ==
    \A w1, w2 \in Txns :
        (w1 # w2 /\ w1 \in cdone /\ w2 \in cdone /\ WSet[w1] \cap WSet[w2] # {})
            => commitTs[w1] < startTs[w2] \/ commitTs[w2] < startTs[w1]
\* A secondary's commit record exists only once its primary's does.
PrimaryDecides ==
    \A w \in Txns : \A k \in WSet[w] \ {Primary[w]} :
        HasCommitRec(k, w) => HasCommitRec(Primary[w], w)
\* A finished transaction committed every key it wrote, or none, and it committed exactly when
\* it took a commit_ts.
AllOrNothing ==
    \A w \in Txns : pc[w] = "Done" =>
        IF commitTs[w] # 0 THEN \A k \in WSet[w] : HasCommitRec(k, w)
        ELSE \A k \in WSet[w] : ~HasCommitRec(k, w)
\* When every thread is done: no lock, no data of a transaction that did not commit, both
\* registries empty, the SSI lock free.
NoLeak ==
    AllDone =>
        /\ \A k \in Keys : lock[k] = 0
        /\ \A k \in Keys : \A d \in data[k] : d.val = 0 \/ HasCommitRec(k, d.val)
        /\ active = {} /\ inflight = {} /\ ssi = 0

\* Every lock is released eventually. (Termination, every process ending, is the translation's.)
LocksReleased == \A k \in Keys : lock[k] # 0 ~> lock[k] = 0

\* The read-only transactions and the safe_read_ts caller.
Readers == {t \in Txns : WSet[t] = {}} \cup Hz
\* They end even when every writer stops anywhere: a read backs off and gives up, and
\* safe_read_ts pins below a writer past its spin cap; neither waits for a writer.
ReadersEnd == \A x \in Readers : <>(pc[x] = "Done")

\* Every thread's steps taken fairly.
FairSpec ==
    /\ Spec
    /\ \A t \in Txns : WF_vars(Tx(t))
    /\ \A x \in Hz : WF_vars(Horizon(x))
    /\ \A g \in Gc : WF_vars(Collector(g))

\* Only the readers' steps taken fairly: a writer may stop anywhere, holding its locks or its
\* registration.
ReadersSpec ==
    /\ Spec
    /\ \A t \in Txns : WSet[t] = {} => WF_vars(Tx(t))
    /\ \A x \in Hz : WF_vars(Horizon(x))

\* Witnesses: each says a case never happens, so a counterexample proves the passing
\* configurations reach it.
Holder(t) == lock[OpK(t, i[t])]
\* A read finds the lock of a transaction that started at or before its timestamp (and may back
\* off, or give up).
NoSightW ==
    \A t \in Txns : ~(pc[t] = "RL" /\ Holder(t) \notin {0, t} /\ startTs[Holder(t)] <= readTs[t])
\* A read finds the lock of a transaction whose primary already committed: a commit half done.
NoHalfReadW ==
    \A t \in Txns : ~(pc[t] = "RL" /\ Holder(t) \in cdone)
\* A read meets an older version than the key's latest commit.
NoOldVersionW ==
    \A t \in Txns : ~(pc[t] = "RW" /\ LatestCommit(wr[OpK(t, i[t])], readTs[t])
                                      # LatestCommit(wr[OpK(t, i[t])], INF))
\* A ReadCommitted read meets a version committed after its transaction's start.
NoFreshRcW ==
    \A t \in Txns : ~(pc[t] = "RW" /\ Iso(t) = "RC"
                      /\ LatestCommit(wr[OpK(t, i[t])], readTs[t]).ts > startTs[t])
\* A prewrite finds another transaction's lock.
NoLockConflictW == \A t \in Txns : ~(pc[t] = "PL" /\ lock[Head(todo[t])] \notin {0, t})
\* A prewrite finds a commit at or after its start_ts.
NoWriteConflictW ==
    \A t \in Txns : ~(pc[t] = "PC" /\ LET r == LatestWrite(wr[Head(todo[t])], INF)
                                      IN r.kind \in {"put", "del"} /\ r.ts >= startTs[t])
\* A prewrite finds a rollback record at or after its start_ts.
NoRollbackRejectW ==
    \A t \in Txns : ~(pc[t] = "PC" /\ LET r == LatestWrite(wr[Head(todo[t])], INF)
                                      IN r.kind = "rb" /\ r.ts >= startTs[t])
\* An SSI validation finds a key of its read set committed after its start_ts.
NoSsiFailW ==
    \A t \in Txns : ~(pc[t] = "SV" /\ \E k \in left[t] :
                          LET r == LatestWrite(wr[k], INF)
                          IN r.kind \in {"put", "del"} /\ r.ts > startTs[t])
\* A transaction's primary committed while a secondary is still locked.
NoHalfCommitW == \A w \in Txns : ~(w \in cdone /\ \E k \in WSet[w] \ {Primary[w]} : lock[k] = w)
\* safe_read_ts answers a horizon below oracle_now.
NoPinW == \A x \in Hz : ~(h[x] # 0 /\ h[x] < now[x])
\* safe_read_ts answers oracle_now after spinning (the writers drained).
NoDrainW == \A x \in Hz : ~(pc[x] = "HZ0" /\ att[x] > 0 /\ h[x] # 0 /\ h[x] = now[x])
\* A min_ts pass is unstable (a register bumped the epoch during it).
NoUnstableW == \A x \in Hz : ~(pc[x] = "HZ4" /\ epoch # bef[x])

\* ---------------------------------------------------------------- programs
R(k) == [op |-> "r", key |-> k]
W(k) == [op |-> "w", key |-> k]
D(k) == [op |-> "d", key |-> k]
T(iso, ops, fin) == [iso |-> iso, ops |-> ops, fin |-> fin]

\* Two writers of keys 1 and 2 with different primaries, and a reader of both.
P_si == [t \in 1 .. 3 |-> CASE t = 1 -> T("RR", <<W(1), W(2)>>, "commit")
                            [] t = 2 -> T("RR", <<W(2), W(1)>>, "commit")
                            [] t = 3 -> T("RR", <<R(1), R(2)>>, "commit")]

\* The same and a second reader, of the keys in the other order.
P_si4 == [t \in 1 .. 4 |-> CASE t = 1 -> T("RR", <<W(1), W(2)>>, "commit")
                             [] t = 2 -> T("RR", <<W(2), W(1)>>, "commit")
                             [] t = 3 -> T("RR", <<R(1), R(2)>>, "commit")
                             [] t = 4 -> T("RR", <<R(2), R(1)>>, "commit")]

\* A writer of keys 1 and 2, a ReadCommitted reader that reads key 1 twice, and a transaction
\* that deletes key 1 (a Delete as its primary) and writes key 2, then deletes it.
P_rc == [t \in 1 .. 3 |-> CASE t = 1 -> T("RR", <<W(1), W(2)>>, "commit")
                            [] t = 2 -> T("RC", <<R(1), R(2), R(1)>>, "commit")
                            [] t = 3 -> T("RR", <<D(1), W(2), D(2)>>, "commit")]

\* Two read-modify-writes of key 1 (the lost update), one reading its own write back, a writer
\* that drops its transaction, and a ReadCommitted read-modify-write of key 2 from key 1.
P_rw == [t \in 1 .. 4 |-> CASE t = 1 -> T("RR", <<R(1), W(1), R(1)>>, "commit")
                            [] t = 2 -> T("RR", <<R(1), W(1)>>, "commit")
                            [] t = 3 -> T("RR", <<W(2), W(1)>>, "drop")
                            [] t = 4 -> T("RC", <<R(1), R(2), W(2)>>, "commit")]

\* The write skew: two Serializable transactions each read the key the other writes; a reader of
\* both that then writes key 1 (behind a rollback record, when the second fails its validation).
P_ser == [t \in 1 .. 3 |-> CASE t = 1 -> T("SER", <<R(1), W(2)>>, "commit")
                             [] t = 2 -> T("SER", <<R(2), W(1)>>, "commit")
                             [] t = 3 -> T("RR", <<R(1), R(2), W(1)>>, "commit")]

\* The same and a read-only Serializable reader of both keys (its commit validates nothing).
P_ser4 == [t \in 1 .. 4 |-> CASE t = 1 -> T("SER", <<R(1), W(2)>>, "commit")
                              [] t = 2 -> T("SER", <<R(2), W(1)>>, "commit")
                              [] t = 3 -> T("RR", <<R(1), R(2), W(1)>>, "commit")
                              [] t = 4 -> T("SER", <<R(2), R(1)>>, "commit")]

\* A Serializable transaction writing keys 2 and 3 after reading key 1, which a second writes.
P_late == [t \in 1 .. 2 |-> CASE t = 1 -> T("SER", <<R(1), W(2), W(3)>>, "commit")
                              [] t = 2 -> T("RR", <<W(1)>>, "commit")]

\* A Serializable transaction that fails its validation (the second writes the key it read), and
\* a third that waits for the SSI lock.
P_kept == [t \in 1 .. 3 |-> CASE t = 1 -> T("SER", <<R(1), W(2)>>, "commit")
                              [] t = 2 -> T("RR", <<W(1)>>, "commit")
                              [] t = 3 -> T("SER", <<W(3)>>, "commit")]

\* A writer of keys 1 and 2 (key 2 its secondary), and a reader of key 2.
P_keep == [t \in 1 .. 2 |-> CASE t = 1 -> T("RR", <<W(1), W(2)>>, "commit")
                              [] t = 2 -> T("RR", <<R(2)>>, "commit")]

\* The masked validation (keys x = 1, y = 2, z = 3): the write skew of P_ser, a third
\* Serializable writer of x that fails its validation (a fourth writes the z it read) and leaves a
\* rollback record on x above the second's commit.
P_mask == [t \in 1 .. 4 |-> CASE t = 1 -> T("SER", <<R(1), W(2)>>, "commit")
                              [] t = 2 -> T("SER", <<R(2), W(1)>>, "commit")
                              [] t = 3 -> T("SER", <<R(3), W(1)>>, "commit")
                              [] t = 4 -> T("RR", <<W(3)>>, "commit")]

\* gc_writes and a rollback record: a Serializable writer of key 1 that fails its validation over
\* key 2, the writer of key 2, and a reader of key 1.
P_gc_rb == [t \in 1 .. 3 |-> CASE t = 1 -> T("SER", <<R(2), W(1)>>, "commit")
                               [] t = 2 -> T("RR", <<W(2)>>, "commit")
                               [] t = 3 -> T("RR", <<R(1)>>, "commit")]

\* gc_data and a prewrite in flight: a writer of key 1 and a reader of it.
P_gc_data == [t \in 1 .. 2 |-> CASE t = 1 -> T("RR", <<W(1)>>, "commit")
                                 [] t = 2 -> T("RR", <<R(1)>>, "commit")]

\* min_active_ts and begin: two readers of key 1.
P_wm == [t \in 1 .. 2 |-> CASE t = 1 -> T("RR", <<R(1)>>, "commit")
                            [] t = 2 -> T("RR", <<R(1)>>, "commit")]

\* The same and a writer of key 1: the version a reader needs collected under it.
P_wm_read == [t \in 1 .. 3 |-> CASE t = 1 -> T("RR", <<R(1)>>, "commit")
                                 [] t = 2 -> T("RR", <<R(1)>>, "commit")
                                 [] t = 3 -> T("RR", <<W(1)>>, "commit")]

\* Two writers in external-apply mode, the embedder registering them, and a safe_read_ts caller.
P_ext == [t \in 1 .. 2 |-> CASE t = 1 -> T("RR", <<W(1)>>, "commit")
                             [] t = 2 -> T("RR", <<W(2), W(1)>>, "commit")]

\* The same and a writer the embedder registers that then drops its transaction.
P_ext3 == [t \in 1 .. 3 |-> CASE t = 1 -> T("RR", <<W(1)>>, "commit")
                              [] t = 2 -> T("RR", <<W(2), W(1)>>, "commit")
                              [] t = 3 -> T("RR", <<W(2)>>, "drop")]

\* A registered writer of keys 2 and 1, a reader of both keys, and the safe_read_ts caller.
P_readers == [t \in 1 .. 2 |-> CASE t = 1 -> T("RR", <<W(2), W(1)>>, "commit")
                                 [] t = 2 -> T("RR", <<R(1), R(2)>>, "commit")]

\* Fairness: a writer of keys 1 and 2, a Serializable reader-writer, a ReadCommitted reader.
P_live == [t \in 1 .. 3 |-> CASE t = 1 -> T("RR", <<W(1), W(2)>>, "commit")
                              [] t = 2 -> T("SER", <<R(1), W(2)>>, "commit")
                              [] t = 3 -> T("RC", <<R(2)>>, "commit")]
=============================================================================
