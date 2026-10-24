--------------------------------- MODULE Stm ---------------------------------
(***************************************************************************)
(* kovan_stm (kovan-stm/src/lib.rs, transaction.rs, var.rs) at the grain   *)
(* of its atomic steps.                                                     *)
(*                                                                          *)
(* A variable (TVar) is a version lock word (a lock bit and a version) and  *)
(* a pointer to a kovan node holding its value, behind a reference count    *)
(* (Arc) that the handles and the transactions' read and write entries      *)
(* share; the last reference to go retires the variable's node. A           *)
(* transaction (one attempt of `atomically`) pins, loads the version clock  *)
(* (its read version), then runs the closure: a load reads the lock word,   *)
(* the pointer and the lock word again, and retries when the variable is    *)
(* locked, newer than the read version, or changed between the two, or,     *)
(* read before, not at the version its first read recorded; a store buffers *)
(* its value in the write set. A read-only transaction commits without      *)
(* validating (each of its reads was). Otherwise the commit locks its write *)
(* set in address order (a load, then a compare-and-swap; a lock held by    *)
(* another committer aborts it), takes the write version with a fetch-add   *)
(* on the clock, validates its read set word by word, then publishes each   *)
(* write: a fresh node swapped in, the old node retired, the version        *)
(* stored. An abort releases the locks it took. kovan frees a retired node, *)
(* dropping its value, once every guard that was pinned when it was retired *)
(* has dropped.                                                             *)
(*                                                                          *)
(* The version clock and every version are kept as their ranks among the    *)
(* numbers in use (renamed at each fetch-add), which keeps every comparison *)
(* the code makes, so the clock never grows out of the state space. The     *)
(* lock word is a pair here; proofs/lean/Kovan/Stm.lean proves the code's   *)
(* packing of it into one u64 decides the same. A thread's private work     *)
(* between two shared steps (a store, a read of its own write, its          *)
(* decisions, a drop of what it owns) is folded into the shared step next   *)
(* to it, which no other thread can tell apart.                             *)
(*                                                                          *)
(* `Mutation` puts back one wrong rule at a time; `Witness` names the one   *)
(* event a witness configuration records. See README.md.                    *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Threads,    \* thread ids, 1 .. 9
    Vars,       \* variable ids, 1 .. 9, in the order of their addresses (a commit locks so)
    Prog,       \* Prog[t]: thread t's transactions, each a sequence of operations (see Op)
    Mutation,   \* "none", or one wrong rule put back
    Witness     \* "none", or the event a witness configuration records

\* An operation of a transaction's closure: <<"r", x>> loads x, <<"w", x>> stores a fresh value
\* in x, <<"retry">> returns Err(Retry) the first time the transaction reaches it, <<"d", x>>
\* drops the closure's handle of x (`Option::take`: on a later attempt the closure skips x).
\* A thread holds a handle of every variable its program names, and drops the rest at its end.

NONE == -1
Min2(a, b) == IF a < b THEN a ELSE b
SetMin(S) == CHOOSE m \in S : \A n \in S : m <= n

\* Value ids: variable x starts with value x; the i-th operation of thread t's j-th transaction
\* stores t * 100 + j * 10 + i. A value is its node: each committed value is in one node.
InitVals == Vars
StoreVal(t, j, i) == t * 100 + j * 10 + i
Places == UNION {UNION {{<<t, j, i>> : i \in 1 .. Len(Prog[t][j])} : j \in 1 .. Len(Prog[t])}
                 : t \in Threads}
StoreVals == {StoreVal(o[1], o[2], o[3]) : o \in {o \in Places : Prog[o[1]][o[2]][o[3]][1] = "w"}}
Values == InitVals \cup StoreVals
ValVar(v) == IF v \in InitVals THEN v ELSE Prog[v \div 100][(v \div 10) % 10][v % 10][2]
VarsOf(t) == {Prog[o[1]][o[2]][o[3]][2] :
              o \in {o \in Places : o[1] = t /\ Prog[o[1]][o[2]][o[3]][1] \in {"r", "w", "d"}}}

ASSUME Threads \subseteq 1 .. 9 /\ Vars \subseteq 1 .. 9
ASSUME \A t \in Threads : Len(Prog[t]) <= 9 /\ \A j \in 1 .. Len(Prog[t]) : Len(Prog[t][j]) <= 9
ASSUME \A x \in Vars : \E t \in Threads : x \in VarsOf(t)

\* commit_copies_value: the code before 01d8a16: the commit publishes a bitwise copy of the value
\* (`ptr::read`) and the write entry, which still owns it, drops it too (DropOnce catches it).
MutCopy == Mutation = "commit_copies_value"
\* keep_locks: the code before 0f88841: a commit that meets a lock held by another committer
\* aborts without releasing the locks it took (LockOwned, and Termination, catch it).
MutKeepLocks == Mutation = "keep_locks"
\* no_var_retire: the code before 7d0c6fe: a variable has no drop, so its last node is never
\* retired (NoLeak catches it).
MutNoVarRetire == Mutation = "no_var_retire"
\* no_keep_alive: the code before 7d0c6fe: a read entry holds a raw pointer to the variable and
\* no reference, so a variable dropped during the transaction is freed under it (NoUseAfterFree
\* catches the validation reading it).
MutNoKeepAlive == Mutation = "no_keep_alive"
\* free_now: the commit frees the node it replaces at once instead of retiring it, so a reader
\* that loaded it under its guard clones a freed node (NoUseAfterFree catches it).
MutFreeNow == Mutation = "free_now"
\* skip_read_validation: the commit of an update transaction skips the read-set validation, as
\* the read-only commit does (Serializable catches the write skew).
MutSkipValidate == Mutation = "skip_read_validation"
\* no_rv_check: a load accepts a version newer than the read version, checking only the lock
\* bit (Opacity catches it).
MutNoRvCheck == Mutation = "no_rv_check"
\* version_before_swap: the commit stores the version (releasing the lock) before swapping the
\* node in, so a reader can take the new version with the old node (AllOrNone catches it).
MutVerFirst == Mutation = "version_before_swap"
\* read_only_not_committed: the read-only commit does not mark the transaction committed, so
\* its drop runs the rollback hooks after a commit (HooksRight catches it).
MutRoFlag == Mutation = "read_only_not_committed"
\* reread_unvalidated: the code before f691cc5: a load of a variable already in the read set
\* loads the pointer again and clones the value with no look at the lock word, so a commit in
\* between shows the transaction a second value (Serializable, Opacity and AllOrNone catch it).
MutRereadShortcut == Mutation = "reread_unvalidated"
\* stale_read_version: a new attempt keeps the read version of the transaction's first attempt
\* instead of loading the clock again, so a variable written since retries it forever
\* (SoloEnds catches it).
MutStaleRv == Mutation = "stale_read_version"

\* The event a witness configuration records (the others record none, at no cost in states).
Ev(e) == IF e = Witness THEN {e} ELSE {}
EvIf(e, c) == IF c /\ e = Witness THEN {e} ELSE {}

\* A variable's references: the handles, every read entry (unless no_keep_alive), every write
\* entry. The variables whose last reference goes when the handles, read sets and write sets
\* become h, r and w are dropped (`TVarInner::drop` retires the node, the Arc frees the rest).
Refs(x, h, r, w) ==
    Cardinality({t \in Threads : x \in h[t]})
        + (IF MutNoKeepAlive THEN 0 ELSE Cardinality({t \in Threads : r[t][x] # NONE}))
        + Cardinality({t \in Threads : w[t][x] # 0})
RetireSet(d, dat) == IF MutNoVarRetire THEN {} ELSE {dat[x] : x \in d}

\* The private operations from the i-th on (stores, a load of a variable the transaction wrote,
\* an operation on a variable whose handle the closure dropped, a retry that already fired) with
\* write set w, handles h and fired retries f: the index of the next shared one (or past the
\* end: the commit), the write set, the values dropped (a second store to a variable drops the
\* first one's value) and the values made.
RECURSIVE Run(_, _, _, _, _, _, _, _)
Run(t, j, i, w, h, f, dr, mk) ==
    IF i > Len(Prog[t][j]) THEN [i |-> i, w |-> w, dr |-> dr, mk |-> mk]
    ELSE LET op == Prog[t][j][i] IN
         IF op[1] = "w" /\ op[2] \in h
         THEN Run(t, j, i + 1, [w EXCEPT ![op[2]] = StoreVal(t, j, i)], h, f,
                  IF w[op[2]] # 0 THEN dr \cup {w[op[2]]} ELSE dr, mk \cup {StoreVal(t, j, i)})
         ELSE IF \/ op[1] \in {"r", "w", "d"} /\ op[2] \notin h
                 \/ op[1] = "r" /\ w[op[2]] # 0
                 \/ op[1] = "retry" /\ i \in f
              THEN Run(t, j, i + 1, w, h, f, dr, mk)
              ELSE [i |-> i, w |-> w, dr |-> dr, mk |-> mk]

\* ------------------------------------------------- serializability and opacity
\* A committed transaction is a record: its id <<thread, transaction>>, the values its attempt
\* read from shared memory (<<variable, value>>), the values it wrote, and the transactions that
\* had returned when the attempt began. P gives each value its place in its variable's order of
\* commits (the initial value 0). b depends on a when b read a's write, overwrote it, overwrote
\* a value a read, or began after a returned.
Dep(a, b, P) ==
    \/ \E r \in b.reads : r \in a.writes
    \/ \E r \in a.writes, s \in b.writes : r[1] = s[1] /\ P[r[2]] < P[s[2]]
    \/ \E r \in a.reads, s \in b.writes : r[1] = s[1] /\ P[r[2]] < P[s[2]]
    \/ a.tx \in b.before
Edges(C, P) ==
    {<<q[1].tx, q[2].tx>> : q \in {q \in C \X C : q[1].tx # q[2].tx /\ Dep(q[1], q[2], P)}}
RECURSIVE Closure(_)
Closure(R) ==
    LET R2 == R \cup {<<q[1][1], q[2][2]>> : q \in {q \in R \X R : q[1][2] = q[2][1]}}
    IN IF R2 = R THEN R ELSE Closure(R2)
Cyclic(R) == \E q \in R : q[1] = q[2]
\* An attempt with reads S, begun after the transactions bf returned, keeps the committed ones C
\* (dependencies closed in T) serializable as a read-only transaction: no transaction that
\* overwrote a value it read reaches one it must follow.
Preds(S, bf, C) == {c.tx : c \in {c \in C : (\E p \in S : p \in c.writes) \/ c.tx \in bf}}
Succs(S, C, P) ==
    {c.tx : c \in {c \in C : \E p \in S, q \in c.writes : q[1] = p[1] /\ P[q[2]] > P[p[2]]}}
Opaque(S, bf, C, P, T) == ~\E s \in Succs(S, C, P), p \in Preds(S, bf, C) : s = p \/ <<s, p>> \in T
\* An attempt that read one write of a committed transaction, and for another variable that
\* transaction wrote a value older than its write, saw the commit torn.
Torn(S, C, P) ==
    \E p \in S, q \in S, c \in C :
        /\ p \in c.writes /\ q[1] # p[1]
        /\ \E r \in c.writes : r[1] = q[1] /\ P[q[2]] < P[r[2]]

(* --algorithm Stm
variables
    \* the version clock; each variable's lock word (lock bit, version) and node
    clock = 0,
    lk = [x \in Vars |-> FALSE],
    ver = [x \in Vars |-> 0],
    data = [x \in Vars |-> x],
    \* the handles each thread holds; a variable whose last reference went is gone (freed)
    hold = [t \in Threads |-> VarsOf(t)],
    gone = [x \in Vars |-> FALSE],
    \* each value's node ("none" until published, "live", "retired", "freed"), its drops, the
    \* threads pinned when it was retired and not unpinned since, the values made so far
    nst = [v \in Values |-> IF v \in InitVals THEN "live" ELSE "none"],
    drops = [v \in Values |-> 0],
    holders = [v \in Values |-> {}],
    made = {},
    \* each thread: its transaction and operation, the retries that fired, whether this is the
    \* transaction's first attempt, its pin, its read version, read set (version read) and
    \* write set (value), the reads its attempt made, a load's first version and node, the
    \* commit's variable in hand, its loaded lock word, its locks, the locks it is releasing, its
    \* write version, and whether its commit was decided
    tj = [t \in Threads |-> 1],
    ti = [t \in Threads |-> 1],
    fired = [t \in Threads |-> {}],
    first = [t \in Threads |-> TRUE],
    pinned = [t \in Threads |-> FALSE],
    rv = [t \in Threads |-> 0],
    rset = [t \in Threads |-> [x \in Vars |-> NONE]],
    wset = [t \in Threads |-> [x \in Vars |-> 0]],
    seen = [t \in Threads |-> {}],
    lv = [t \in Threads |-> 0],
    ln = [t \in Threads |-> 0],
    cx = [t \in Threads |-> 0],
    cur = [t \in Threads |-> 0],
    lkd = [t \in Threads |-> {}],
    ul = [t \in Threads |-> {}],
    wv = [t \in Threads |-> 0],
    dec = [t \in Threads |-> FALSE],
    \* histories: each value's place in its variable's order of commits, the commits of each
    \* variable, the committed transactions and the closure of their dependencies, the
    \* transactions that returned, those that had when each attempt began, the broken checks,
    \* the witness events
    pos = [v \in Values |-> IF v \in InitVals THEN 0 ELSE NONE],
    pubs = [x \in Vars |-> 0],
    commits = {},
    tc = {},
    done = {},
    before = [t \in Threads |-> {}],
    errs = {},
    ev = {};

define
    Op(t) == Prog[t][tj[t]][ti[t]]
    OpVar(t) == Prog[t][tj[t]][ti[t]][2]
    WVars(t) == {x \in Vars : wset[t][x] # 0}
    \* the read entries a commit validates: those it did not also write
    VVars(t) == {x \in Vars : rset[t][x] # NONE /\ wset[t][x] = 0}
    Pinned == {t \in Threads : pinned[t]}
    Dying(h, r, w) == {x \in Vars : ~gone[x] /\ Refs(x, h, r, w) = 0}
    PendingOf(t) == {wset[t][x] : x \in Vars} \ {0}
    \* a node dereferenced: freed, or its value dropped, is a use after free
    Deref(n) == IF nst[n] = "freed" \/ drops[n] > 0 THEN {"uaf"} ELSE {}
    \* a variable's lock word or pointer touched after the variable was freed
    TouchVar(x) == IF gone[x] THEN {"uaf"} ELSE {}
    ReadErrs(t, S, n) ==
        Deref(n)
            \cup (IF Opaque(S, before[t], commits, pos, tc) THEN {} ELSE {"opacity"})
            \cup (IF Torn(S, commits, pos) THEN {"torn"} ELSE {})
    \* The numbers in use; each is renamed to its rank at a fetch-add of the clock.
    Live ==
        {0, clock + 1} \cup {ver[x] : x \in Vars} \cup {rv[t] : t \in Threads}
            \cup {lv[t] : t \in Threads} \cup {cur[t] : t \in Threads} \cup {wv[t] : t \in Threads}
            \cup ({rset[t][x] : t \in Threads, x \in Vars} \ {NONE})
    Rank(n) == Cardinality({m \in Live : m < n})
    AllDone == \A t \in Threads : pc[t] = "Done"
end define;

\* The private operations from the i0-th on, applied (see Run), with the extra broken checks e.
macro Advance(i0, e)
begin
    with r = Run(self, tj[self], i0, wset[self], hold[self], fired[self], {}, {}) do
        ti[self] := r.i || wset[self] := r.w || made := made \cup r.mk
            || drops := [v \in Values |->
                            IF v \in r.mk THEN (IF v \in r.dr THEN 1 ELSE 0)
                            ELSE IF v \in r.dr THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
            \* a value made again whose earlier making was never dropped leaked
            || errs := errs \cup e
                \cup (IF \E v \in r.mk : v \in made /\ drops[v] = 0 THEN {"leak"} ELSE {})
                \cup (IF \E v \in r.dr \ r.mk : drops[v] >= 1 THEN {"double_drop"} ELSE {});
    end with;
end macro;

\* The attempt's end: the transaction dropped (the write set's values, none left after a
\* commit; every entry's reference, a variable losing its last one dropped; the rollback hooks
\* unless the transaction is marked committed), then the guard dropped. `committed` is the
\* code's flag, `decided` whether the commit was decided, e and evs extra checks and events.
macro Teardown(committed, decided, e, evs)
begin
    with nr = [rset EXCEPT ![self] = [y \in Vars |-> NONE]],
         nw = [wset EXCEPT ![self] = [y \in Vars |-> 0]],
         d = Dying(hold, nr, nw),
         rn = RetireSet(d, data),
         pend = PendingOf(self) do
        drops := [v \in Values |-> IF v \in pend THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
            || nst := [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
            || holders := [v \in Values |-> (IF v \in rn THEN Pinned ELSE holders[v]) \ {self}]
            || gone := [y \in Vars |-> gone[y] \/ y \in d]
            || rset := nr || wset := nw || seen[self] := {} || pinned[self] := FALSE
            || lkd[self] := {} || ul[self] := {} || lv[self] := 0 || ln[self] := 0
            || cur[self] := 0 || wv[self] := 0 || cx[self] := 0
            || errs := errs \cup e
                \cup (IF \E v \in pend : drops[v] >= 1 THEN {"double_drop"} ELSE {})
                \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                \* the rollback hooks run on a commit
                \cup (IF ~committed /\ decided THEN {"hooks"} ELSE {})
            || ev := ev \cup evs \cup EvIf("entry_drop", d # {});
    end with;
end macro;

\* The commit decided (its validation passed): its writes take the next places of their
\* variables' orders; the committed transactions must stay serializable and every other running
\* attempt opaque. e: extra broken checks.
macro Decide(e)
begin
    with np = [v \in Values |-> IF \E y \in Vars : wset[self][y] = v
                                THEN pubs[ValVar(v)] + 1 ELSE pos[v]],
         c = [tx |-> <<self, tj[self]>>, reads |-> seen[self],
              writes |-> {<<y, wset[self][y]>> : y \in WVars(self)}, before |-> before[self]],
         nc = commits \cup {c},
         nt = Closure(Edges(nc, np)) do
        pos := np || pubs := [y \in Vars |-> IF y \in WVars(self) THEN pubs[y] + 1 ELSE pubs[y]]
            || commits := nc || tc := nt || dec[self] := TRUE
            || errs := errs \cup e
                \cup (IF Cyclic(nt) THEN {"not_serializable"} ELSE {})
                \cup (IF \A u \in Threads \ {self} : Opaque(seen[u], before[u], nc, np, nt)
                      THEN {} ELSE {"opacity"});
    end with;
end macro;

\* Write::commit's swap: a fresh node holding the value in, the node it replaces retired (or,
\* mutated, freed at once, its value dropped).
macro Swap()
begin
    data[cx[self]] := wset[self][cx[self]]
        || nst := [nst EXCEPT ![wset[self][cx[self]]] = "live",
                              ![data[cx[self]]] = IF MutFreeNow THEN "freed" ELSE "retired"]
        || holders[data[cx[self]]] := Pinned
        || drops[data[cx[self]]] := IF MutFreeNow THEN Min2(drops[data[cx[self]]] + 1, 2)
                                    ELSE drops[data[cx[self]]];
end macro;

process Thread \in Threads
begin
TX:
    if tj[self] > Len(Prog[self]) then
        \* the thread ends: it drops the handles it still holds (a variable's drop pins a guard
        \* of its own around retiring the node)
        with nh = [hold EXCEPT ![self] = {}], d = Dying(nh, rset, wset), rn = RetireSet(d, data) do
            hold := nh || gone := [x \in Vars |-> gone[x] \/ x \in d]
                || nst := [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                || holders := [v \in Values |-> IF v \in rn THEN Pinned ELSE holders[v]]
                || errs := errs
                    \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {});
        end with;
        goto Done;
    else
        \* atomically: the pin, then Transaction::new loads the clock (the read version); the
        \* closure runs up to its first shared operation
        pinned[self] := TRUE || before[self] := done || dec[self] := FALSE
            || rv[self] := IF MutStaleRv /\ ~first[self] THEN rv[self] ELSE clock;
        Advance(1, {});
        goto OP;
    end if;
OP:
    if ti[self] > Len(Prog[self][tj[self]]) then
        if WVars(self) = {} then
            \* commit, read-only: no validation; marked committed, the commit hooks, the drop
            with c = [tx |-> <<self, tj[self]>>, reads |-> seen[self], writes |-> {},
                      before |-> before[self]],
                 nc = commits \cup {c},
                 nt = Closure(Edges(nc, pos)) do
                commits := nc || tc := nt || done := done \cup {c.tx}
                    || tj[self] := tj[self] + 1 || first[self] := TRUE || fired[self] := {}
                    || rv[self] := 0;
                Teardown(~MutRoFlag, TRUE,
                         (IF Cyclic(nt) THEN {"not_serializable"} ELSE {})
                             \cup (IF \A u \in Threads \ {self} :
                                        Opaque(seen[u], before[u], nc, pos, nt)
                                   THEN {} ELSE {"opacity"}),
                         {});
            end with;
            goto TX;
        else
            \* commit: the first variable of the write set, its lock word loaded
            if lk[SetMin(WVars(self))] then
                \* held by another committer: abort, no lock taken yet
                first[self] := FALSE;
                Teardown(FALSE, FALSE, {}, Ev("lock_abort"));
                goto TX;
            else
                cx[self] := SetMin(WVars(self)) || cur[self] := ver[SetMin(WVars(self))];
                goto LK2;
            end if;
        end if;
    elsif Op(self)[1] = "r" then
        if MutRereadShortcut /\ rset[self][OpVar(self)] # NONE then
            \* (reread_unvalidated) a variable in the read set: its pointer loaded again, with
            \* no version check
            ln[self] := data[OpVar(self)];
            goto RD4;
        elsif lk[OpVar(self)] \/ (~MutNoRvCheck /\ ver[OpVar(self)] > rv[self]) then
            \* load: the lock word first; locked, or newer than the read version: Retry
            first[self] := FALSE;
            Teardown(FALSE, FALSE, {},
                     Ev("read_retry") \cup EvIf("reread_retry", rset[self][OpVar(self)] # NONE));
            goto TX;
        else
            lv[self] := ver[OpVar(self)];
            goto RD2;
        end if;
    elsif Op(self)[1] = "retry" then
        \* the closure returns Err(Retry): the transaction dropped, a new attempt
        fired[self] := fired[self] \cup {ti[self]} || first[self] := FALSE;
        Teardown(FALSE, FALSE, {}, {});
        goto TX;
    else
        \* the closure drops its handle: the reference released, the last one drops the variable
        with x = OpVar(self), nh = [hold EXCEPT ![self] = @ \ {x}], d = Dying(nh, rset, wset),
             rn = RetireSet(d, data),
             bad = IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {} do
            hold := nh || gone := [y \in Vars |-> gone[y] \/ y \in d]
                || nst := [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                || holders := [v \in Values |-> IF v \in rn THEN Pinned ELSE holders[v]];
            Advance(ti[self] + 1, bad);
        end with;
        goto OP;
    end if;
RD2: \* load: the pointer
    ln[self] := data[OpVar(self)];
RD3: \* load: the lock word again; changed or locked since: Retry. A variable read before must
     \* have the version the first read recorded, else Retry; one read first is recorded.
    if \/ lk[OpVar(self)] \/ ver[OpVar(self)] # lv[self]
       \/ rset[self][OpVar(self)] \notin {NONE, lv[self]} then
        first[self] := FALSE;
        Teardown(FALSE, FALSE, {},
                 Ev("post_retry")
                     \cup EvIf("reread_version", ~lk[OpVar(self)] /\ ver[OpVar(self)] = lv[self]));
        goto TX;
    else
        rset[self][OpVar(self)] := lv[self] || lv[self] := 0
            || ev := ev \cup EvIf("reread", rset[self][OpVar(self)] # NONE);
    end if;
RD4: \* the node's value cloned: the closure has it
    with x = OpVar(self), n = ln[self], s = seen[self] \cup {<<x, n>>} do
        seen[self] := s || ln[self] := 0;
        Advance(ti[self] + 1, ReadErrs(self, s, n));
    end with;
    goto OP;
LK1: \* commit: the next variable's lock word loaded; held by another committer: abort
    if lk[cx[self]] then
        if lkd[self] = {} \/ MutKeepLocks then
            first[self] := FALSE;
            Teardown(FALSE, FALSE, {}, Ev("lock_abort"));
            goto TX;
        else
            ul[self] := lkd[self] || ev := ev \cup Ev("lock_abort");
            goto UL;
        end if;
    else
        cur[self] := ver[cx[self]];
    end if;
LK2: \* the lock word's compare-and-swap from the word loaded to it locked
    if ~lk[cx[self]] /\ ver[cx[self]] = cur[self] then
        lk[cx[self]] := TRUE || lkd[self] := lkd[self] \cup {cx[self]};
        if rset[self][cx[self]] # NONE /\ cur[self] > rset[self][cx[self]] then
            \* read, then written by another commit: abort, releasing this lock and those before
            ul[self] := lkd[self] || ev := ev \cup Ev("version_abort");
            goto UL;
        elsif \E y \in WVars(self) : y > cx[self] then
            cx[self] := SetMin({y \in WVars(self) : y > cx[self]});
            goto LK1;
        else
            goto CK;
        end if;
    elsif lk[cx[self]] then
        \* the compare-and-swap failed on a word another committer locked: abort
        if lkd[self] = {} \/ MutKeepLocks then
            first[self] := FALSE;
            Teardown(FALSE, FALSE, {}, Ev("lock_abort"));
            goto TX;
        else
            ul[self] := lkd[self] || ev := ev \cup Ev("lock_abort");
            goto UL;
        end if;
    else
        \* it failed on a word a commit changed: again, with that word
        cur[self] := ver[cx[self]];
        goto LK2;
    end if;
CK: \* the write version: the clock's fetch-add (every number renamed to its rank)
    clock := Rank(clock + 1)
        || wv := [t \in Threads |-> IF t = self THEN Rank(clock + 1) ELSE Rank(wv[t])]
        || ver := [x \in Vars |-> Rank(ver[x])]
        || rv := [t \in Threads |-> Rank(rv[t])]
        || lv := [t \in Threads |-> Rank(lv[t])]
        || cur := [t \in Threads |-> Rank(cur[t])]
        || rset := [t \in Threads |-> [x \in Vars |->
                        IF rset[t][x] = NONE THEN NONE ELSE Rank(rset[t][x])]];
    if MutSkipValidate \/ VVars(self) = {} then
        Decide({});
        cx[self] := SetMin(WVars(self));
        goto PB1;
    else
        cx[self] := SetMin(VVars(self));
    end if;
VA: \* validation: the next read entry's lock word; locked, or newer than read: abort
    if lk[cx[self]] \/ ver[cx[self]] > rset[self][cx[self]] then
        ul[self] := lkd[self] || ev := ev \cup Ev("validate_abort")
            || errs := errs \cup TouchVar(cx[self]);
        goto UL;
    elsif \E y \in VVars(self) : y > cx[self] then
        errs := errs \cup TouchVar(cx[self])
            || cx[self] := SetMin({y \in VVars(self) : y > cx[self]});
        goto VA;
    else
        Decide(TouchVar(cx[self]));
        cx[self] := SetMin(WVars(self));
    end if;
PB1: \* Write::commit: the swap (or, mutated, the version store first)
    if MutVerFirst then
        ver[cx[self]] := wv[self] || lk[cx[self]] := FALSE || lkd[self] := lkd[self] \ {cx[self]};
    else
        Swap();
    end if;
PB2: \* the version stored, which releases the lock (or, mutated, the swap); then the write
     \* entry's reference to the variable dropped (the last one drops the variable)
    with nw = [wset EXCEPT ![self][cx[self]] = 0],
         old = data[cx[self]],
         new = wset[self][cx[self]],
         dat = IF MutVerFirst THEN [data EXCEPT ![cx[self]] = wset[self][cx[self]]] ELSE data,
         d = Dying(hold, rset, nw),
         rn = RetireSet(d, dat) do
        wset := nw || data := dat
            || ver[cx[self]] := IF MutVerFirst THEN ver[cx[self]] ELSE wv[self]
            || lk[cx[self]] := IF MutVerFirst THEN lk[cx[self]] ELSE FALSE
            || lkd[self] := lkd[self] \ {cx[self]}
            || nst := [v \in Values |->
                          IF v \in rn THEN "retired"
                          ELSE IF MutVerFirst /\ v = new THEN "live"
                          ELSE IF MutVerFirst /\ v = old THEN "retired" ELSE nst[v]]
            || holders := [v \in Values |->
                              IF v \in rn \/ (MutVerFirst /\ v = old) THEN Pinned ELSE holders[v]]
            || gone := [y \in Vars |-> gone[y] \/ y \in d]
            \* (commit_copies_value) the write entry drops the value the node holds a copy of
            || drops := [drops EXCEPT ![new] = IF MutCopy THEN Min2(@ + 1, 2) ELSE @]
            || errs := errs
                \cup (IF \E v \in rn : nst[v] # "live" /\ v # new THEN {"double_drop"} ELSE {})
            || ev := ev \cup EvIf("commit_var_drop", d # {});
    end with;
    if \E y \in WVars(self) : y > cx[self] then
        cx[self] := SetMin({y \in WVars(self) : y > cx[self]});
        goto PB1;
    end if;
FIN: \* the commit returns true: marked committed, the commit hooks (every lock released by now),
     \* the transaction dropped, the guard dropped
    done := done \cup {<<self, tj[self]>>} || tj[self] := tj[self] + 1 || first[self] := TRUE
        || fired[self] := {} || rv[self] := 0;
    Teardown(TRUE, TRUE, IF \E y \in Vars : lk[y] /\ y \in lkd[self] THEN {"hooks"} ELSE {}, {});
    goto TX;
UL: \* abort: the next lock this commit took cleared (fetch_and), its version left as it was
    lk[SetMin(ul[self])] := FALSE;
    if ul[self] = {SetMin(ul[self])} then
        first[self] := FALSE;
        Teardown(FALSE, FALSE, {}, {});
        goto TX;
    else
        ul[self] := ul[self] \ {SetMin(ul[self])} || lkd[self] := lkd[self] \ {SetMin(ul[self])};
        goto UL;
    end if;
end process;

\* kovan's reclamation: a retired node is freed, its value dropped, once every guard that was
\* pinned when it was retired has dropped (retire_node; the guard's drop).
process Reclaimer = 0
begin
RC1:
    while ~(AllDone /\ \A v \in Values : nst[v] # "retired") do
        with v \in {u \in Values : nst[u] = "retired" /\ holders[u] = {}} do
            nst[v] := "freed" || drops[v] := Min2(drops[v] + 1, 2)
                || errs := errs \cup (IF drops[v] >= 1 THEN {"double_drop"} ELSE {});
        end with;
    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "6886c9c9" /\ chksum(tla) = "4ce92581")
VARIABLES clock, lk, ver, data, hold, gone, nst, drops, holders, made, tj, ti, 
          fired, first, pinned, rv, rset, wset, seen, lv, ln, cx, cur, lkd, 
          ul, wv, dec, pos, pubs, commits, tc, done, before, errs, ev, pc

(* define statement *)
Op(t) == Prog[t][tj[t]][ti[t]]
OpVar(t) == Prog[t][tj[t]][ti[t]][2]
WVars(t) == {x \in Vars : wset[t][x] # 0}

VVars(t) == {x \in Vars : rset[t][x] # NONE /\ wset[t][x] = 0}
Pinned == {t \in Threads : pinned[t]}
Dying(h, r, w) == {x \in Vars : ~gone[x] /\ Refs(x, h, r, w) = 0}
PendingOf(t) == {wset[t][x] : x \in Vars} \ {0}

Deref(n) == IF nst[n] = "freed" \/ drops[n] > 0 THEN {"uaf"} ELSE {}

TouchVar(x) == IF gone[x] THEN {"uaf"} ELSE {}
ReadErrs(t, S, n) ==
    Deref(n)
        \cup (IF Opaque(S, before[t], commits, pos, tc) THEN {} ELSE {"opacity"})
        \cup (IF Torn(S, commits, pos) THEN {"torn"} ELSE {})

Live ==
    {0, clock + 1} \cup {ver[x] : x \in Vars} \cup {rv[t] : t \in Threads}
        \cup {lv[t] : t \in Threads} \cup {cur[t] : t \in Threads} \cup {wv[t] : t \in Threads}
        \cup ({rset[t][x] : t \in Threads, x \in Vars} \ {NONE})
Rank(n) == Cardinality({m \in Live : m < n})
AllDone == \A t \in Threads : pc[t] = "Done"


vars == << clock, lk, ver, data, hold, gone, nst, drops, holders, made, tj, 
           ti, fired, first, pinned, rv, rset, wset, seen, lv, ln, cx, cur, 
           lkd, ul, wv, dec, pos, pubs, commits, tc, done, before, errs, ev, 
           pc >>

ProcSet == (Threads) \cup {0}

Init == (* Global variables *)
        /\ clock = 0
        /\ lk = [x \in Vars |-> FALSE]
        /\ ver = [x \in Vars |-> 0]
        /\ data = [x \in Vars |-> x]
        /\ hold = [t \in Threads |-> VarsOf(t)]
        /\ gone = [x \in Vars |-> FALSE]
        /\ nst = [v \in Values |-> IF v \in InitVals THEN "live" ELSE "none"]
        /\ drops = [v \in Values |-> 0]
        /\ holders = [v \in Values |-> {}]
        /\ made = {}
        /\ tj = [t \in Threads |-> 1]
        /\ ti = [t \in Threads |-> 1]
        /\ fired = [t \in Threads |-> {}]
        /\ first = [t \in Threads |-> TRUE]
        /\ pinned = [t \in Threads |-> FALSE]
        /\ rv = [t \in Threads |-> 0]
        /\ rset = [t \in Threads |-> [x \in Vars |-> NONE]]
        /\ wset = [t \in Threads |-> [x \in Vars |-> 0]]
        /\ seen = [t \in Threads |-> {}]
        /\ lv = [t \in Threads |-> 0]
        /\ ln = [t \in Threads |-> 0]
        /\ cx = [t \in Threads |-> 0]
        /\ cur = [t \in Threads |-> 0]
        /\ lkd = [t \in Threads |-> {}]
        /\ ul = [t \in Threads |-> {}]
        /\ wv = [t \in Threads |-> 0]
        /\ dec = [t \in Threads |-> FALSE]
        /\ pos = [v \in Values |-> IF v \in InitVals THEN 0 ELSE NONE]
        /\ pubs = [x \in Vars |-> 0]
        /\ commits = {}
        /\ tc = {}
        /\ done = {}
        /\ before = [t \in Threads |-> {}]
        /\ errs = {}
        /\ ev = {}
        /\ pc = [self \in ProcSet |-> CASE self \in Threads -> "TX"
                                        [] self = 0 -> "RC1"]

TX(self) == /\ pc[self] = "TX"
            /\ IF tj[self] > Len(Prog[self])
                  THEN /\ LET nh == [hold EXCEPT ![self] = {}] IN
                            LET d == Dying(nh, rset, wset) IN
                              LET rn == RetireSet(d, data) IN
                                /\ errs' =        errs
                                           \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                                /\ gone' = [x \in Vars |-> gone[x] \/ x \in d]
                                /\ hold' = nh
                                /\ holders' = [v \in Values |-> IF v \in rn THEN Pinned ELSE holders[v]]
                                /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << drops, made, ti, pinned, rv, wset, dec, 
                                       before >>
                  ELSE /\ /\ before' = [before EXCEPT ![self] = done]
                          /\ dec' = [dec EXCEPT ![self] = FALSE]
                          /\ pinned' = [pinned EXCEPT ![self] = TRUE]
                          /\ rv' = [rv EXCEPT ![self] = IF MutStaleRv /\ ~first[self] THEN rv[self] ELSE clock]
                       /\ LET r == Run(self, tj[self], 1, wset[self], hold[self], fired[self], {}, {}) IN
                            /\ drops' = [v \in Values |->
                                            IF v \in r.mk THEN (IF v \in r.dr THEN 1 ELSE 0)
                                            ELSE IF v \in r.dr THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                            /\ errs' = (       errs \cup ({})
                                        \cup (IF \E v \in r.mk : v \in made /\ drops[v] = 0 THEN {"leak"} ELSE {})
                                        \cup (IF \E v \in r.dr \ r.mk : drops[v] >= 1 THEN {"double_drop"} ELSE {}))
                            /\ made' = (made \cup r.mk)
                            /\ ti' = [ti EXCEPT ![self] = r.i]
                            /\ wset' = [wset EXCEPT ![self] = r.w]
                       /\ pc' = [pc EXCEPT ![self] = "OP"]
                       /\ UNCHANGED << hold, gone, nst, holders >>
            /\ UNCHANGED << clock, lk, ver, data, tj, fired, first, rset, seen, 
                            lv, ln, cx, cur, lkd, ul, wv, pos, pubs, commits, 
                            tc, done, ev >>

OP(self) == /\ pc[self] = "OP"
            /\ IF ti[self] > Len(Prog[self][tj[self]])
                  THEN /\ IF WVars(self) = {}
                             THEN /\ LET c == [tx |-> <<self, tj[self]>>, reads |-> seen[self], writes |-> {},
                                               before |-> before[self]] IN
                                       LET nc == commits \cup {c} IN
                                         LET nt == Closure(Edges(nc, pos)) IN
                                           /\ /\ commits' = nc
                                              /\ done' = (done \cup {c.tx})
                                              /\ fired' = [fired EXCEPT ![self] = {}]
                                              /\ first' = [first EXCEPT ![self] = TRUE]
                                              /\ rv' = [rv EXCEPT ![self] = 0]
                                              /\ tc' = nt
                                              /\ tj' = [tj EXCEPT ![self] = tj[self] + 1]
                                           /\ LET nr == [rset EXCEPT ![self] = [y \in Vars |-> NONE]] IN
                                                LET nw == [wset EXCEPT ![self] = [y \in Vars |-> 0]] IN
                                                  LET d == Dying(hold, nr, nw) IN
                                                    LET rn == RetireSet(d, data) IN
                                                      LET pend == PendingOf(self) IN
                                                        /\ cur' = [cur EXCEPT ![self] = 0]
                                                        /\ cx' = [cx EXCEPT ![self] = 0]
                                                        /\ drops' = [v \in Values |-> IF v \in pend THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                                                        /\ errs' = (       errs \cup ((IF Cyclic(nt) THEN {"not_serializable"} ELSE {})
                                                                                          \cup (IF \A u \in Threads \ {self} :
                                                                                                     Opaque(seen[u], before[u], nc, pos, nt)
                                                                                                THEN {} ELSE {"opacity"}))
                                                                    \cup (IF \E v \in pend : drops[v] >= 1 THEN {"double_drop"} ELSE {})
                                                                    \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                                                                    
                                                                    \cup (IF ~(~MutRoFlag) /\ TRUE THEN {"hooks"} ELSE {}))
                                                        /\ ev' = (ev \cup ({}) \cup EvIf("entry_drop", d # {}))
                                                        /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                                                        /\ holders' = [v \in Values |-> (IF v \in rn THEN Pinned ELSE holders[v]) \ {self}]
                                                        /\ lkd' = [lkd EXCEPT ![self] = {}]
                                                        /\ ln' = [ln EXCEPT ![self] = 0]
                                                        /\ lv' = [lv EXCEPT ![self] = 0]
                                                        /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                                                        /\ pinned' = [pinned EXCEPT ![self] = FALSE]
                                                        /\ rset' = nr
                                                        /\ seen' = [seen EXCEPT ![self] = {}]
                                                        /\ ul' = [ul EXCEPT ![self] = {}]
                                                        /\ wset' = nw
                                                        /\ wv' = [wv EXCEPT ![self] = 0]
                                  /\ pc' = [pc EXCEPT ![self] = "TX"]
                             ELSE /\ IF lk[SetMin(WVars(self))]
                                        THEN /\ first' = [first EXCEPT ![self] = FALSE]
                                             /\ LET nr == [rset EXCEPT ![self] = [y \in Vars |-> NONE]] IN
                                                  LET nw == [wset EXCEPT ![self] = [y \in Vars |-> 0]] IN
                                                    LET d == Dying(hold, nr, nw) IN
                                                      LET rn == RetireSet(d, data) IN
                                                        LET pend == PendingOf(self) IN
                                                          /\ cur' = [cur EXCEPT ![self] = 0]
                                                          /\ cx' = [cx EXCEPT ![self] = 0]
                                                          /\ drops' = [v \in Values |-> IF v \in pend THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                                                          /\ errs' = (       errs \cup ({})
                                                                      \cup (IF \E v \in pend : drops[v] >= 1 THEN {"double_drop"} ELSE {})
                                                                      \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                                                                      
                                                                      \cup (IF ~FALSE /\ FALSE THEN {"hooks"} ELSE {}))
                                                          /\ ev' = (ev \cup (Ev("lock_abort")) \cup EvIf("entry_drop", d # {}))
                                                          /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                                                          /\ holders' = [v \in Values |-> (IF v \in rn THEN Pinned ELSE holders[v]) \ {self}]
                                                          /\ lkd' = [lkd EXCEPT ![self] = {}]
                                                          /\ ln' = [ln EXCEPT ![self] = 0]
                                                          /\ lv' = [lv EXCEPT ![self] = 0]
                                                          /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                                                          /\ pinned' = [pinned EXCEPT ![self] = FALSE]
                                                          /\ rset' = nr
                                                          /\ seen' = [seen EXCEPT ![self] = {}]
                                                          /\ ul' = [ul EXCEPT ![self] = {}]
                                                          /\ wset' = nw
                                                          /\ wv' = [wv EXCEPT ![self] = 0]
                                             /\ pc' = [pc EXCEPT ![self] = "TX"]
                                        ELSE /\ /\ cur' = [cur EXCEPT ![self] = ver[SetMin(WVars(self))]]
                                                /\ cx' = [cx EXCEPT ![self] = SetMin(WVars(self))]
                                             /\ pc' = [pc EXCEPT ![self] = "LK2"]
                                             /\ UNCHANGED << gone, nst, drops, 
                                                             holders, first, 
                                                             pinned, rset, 
                                                             wset, seen, lv, 
                                                             ln, lkd, ul, wv, 
                                                             errs, ev >>
                                  /\ UNCHANGED << tj, fired, rv, commits, tc, 
                                                  done >>
                       /\ UNCHANGED << hold, made, ti >>
                  ELSE /\ IF Op(self)[1] = "r"
                             THEN /\ IF MutRereadShortcut /\ rset[self][OpVar(self)] # NONE
                                        THEN /\ ln' = [ln EXCEPT ![self] = data[OpVar(self)]]
                                             /\ pc' = [pc EXCEPT ![self] = "RD4"]
                                             /\ UNCHANGED << gone, nst, drops, 
                                                             holders, first, 
                                                             pinned, rset, 
                                                             wset, seen, lv, 
                                                             cx, cur, lkd, ul, 
                                                             wv, errs, ev >>
                                        ELSE /\ IF lk[OpVar(self)] \/ (~MutNoRvCheck /\ ver[OpVar(self)] > rv[self])
                                                   THEN /\ first' = [first EXCEPT ![self] = FALSE]
                                                        /\ LET nr == [rset EXCEPT ![self] = [y \in Vars |-> NONE]] IN
                                                             LET nw == [wset EXCEPT ![self] = [y \in Vars |-> 0]] IN
                                                               LET d == Dying(hold, nr, nw) IN
                                                                 LET rn == RetireSet(d, data) IN
                                                                   LET pend == PendingOf(self) IN
                                                                     /\ cur' = [cur EXCEPT ![self] = 0]
                                                                     /\ cx' = [cx EXCEPT ![self] = 0]
                                                                     /\ drops' = [v \in Values |-> IF v \in pend THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                                                                     /\ errs' = (       errs \cup ({})
                                                                                 \cup (IF \E v \in pend : drops[v] >= 1 THEN {"double_drop"} ELSE {})
                                                                                 \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                                                                                 
                                                                                 \cup (IF ~FALSE /\ FALSE THEN {"hooks"} ELSE {}))
                                                                     /\ ev' = (ev \cup (Ev("read_retry") \cup EvIf("reread_retry", rset[self][OpVar(self)] # NONE)) \cup EvIf("entry_drop", d # {}))
                                                                     /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                                                                     /\ holders' = [v \in Values |-> (IF v \in rn THEN Pinned ELSE holders[v]) \ {self}]
                                                                     /\ lkd' = [lkd EXCEPT ![self] = {}]
                                                                     /\ ln' = [ln EXCEPT ![self] = 0]
                                                                     /\ lv' = [lv EXCEPT ![self] = 0]
                                                                     /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                                                                     /\ pinned' = [pinned EXCEPT ![self] = FALSE]
                                                                     /\ rset' = nr
                                                                     /\ seen' = [seen EXCEPT ![self] = {}]
                                                                     /\ ul' = [ul EXCEPT ![self] = {}]
                                                                     /\ wset' = nw
                                                                     /\ wv' = [wv EXCEPT ![self] = 0]
                                                        /\ pc' = [pc EXCEPT ![self] = "TX"]
                                                   ELSE /\ lv' = [lv EXCEPT ![self] = ver[OpVar(self)]]
                                                        /\ pc' = [pc EXCEPT ![self] = "RD2"]
                                                        /\ UNCHANGED << gone, 
                                                                        nst, 
                                                                        drops, 
                                                                        holders, 
                                                                        first, 
                                                                        pinned, 
                                                                        rset, 
                                                                        wset, 
                                                                        seen, 
                                                                        ln, cx, 
                                                                        cur, 
                                                                        lkd, 
                                                                        ul, wv, 
                                                                        errs, 
                                                                        ev >>
                                  /\ UNCHANGED << hold, made, ti, fired >>
                             ELSE /\ IF Op(self)[1] = "retry"
                                        THEN /\ /\ fired' = [fired EXCEPT ![self] = fired[self] \cup {ti[self]}]
                                                /\ first' = [first EXCEPT ![self] = FALSE]
                                             /\ LET nr == [rset EXCEPT ![self] = [y \in Vars |-> NONE]] IN
                                                  LET nw == [wset EXCEPT ![self] = [y \in Vars |-> 0]] IN
                                                    LET d == Dying(hold, nr, nw) IN
                                                      LET rn == RetireSet(d, data) IN
                                                        LET pend == PendingOf(self) IN
                                                          /\ cur' = [cur EXCEPT ![self] = 0]
                                                          /\ cx' = [cx EXCEPT ![self] = 0]
                                                          /\ drops' = [v \in Values |-> IF v \in pend THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                                                          /\ errs' = (       errs \cup ({})
                                                                      \cup (IF \E v \in pend : drops[v] >= 1 THEN {"double_drop"} ELSE {})
                                                                      \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                                                                      
                                                                      \cup (IF ~FALSE /\ FALSE THEN {"hooks"} ELSE {}))
                                                          /\ ev' = (ev \cup ({}) \cup EvIf("entry_drop", d # {}))
                                                          /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                                                          /\ holders' = [v \in Values |-> (IF v \in rn THEN Pinned ELSE holders[v]) \ {self}]
                                                          /\ lkd' = [lkd EXCEPT ![self] = {}]
                                                          /\ ln' = [ln EXCEPT ![self] = 0]
                                                          /\ lv' = [lv EXCEPT ![self] = 0]
                                                          /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                                                          /\ pinned' = [pinned EXCEPT ![self] = FALSE]
                                                          /\ rset' = nr
                                                          /\ seen' = [seen EXCEPT ![self] = {}]
                                                          /\ ul' = [ul EXCEPT ![self] = {}]
                                                          /\ wset' = nw
                                                          /\ wv' = [wv EXCEPT ![self] = 0]
                                             /\ pc' = [pc EXCEPT ![self] = "TX"]
                                             /\ UNCHANGED << hold, made, ti >>
                                        ELSE /\ LET x == OpVar(self) IN
                                                  LET nh == [hold EXCEPT ![self] = @ \ {x}] IN
                                                    LET d == Dying(nh, rset, wset) IN
                                                      LET rn == RetireSet(d, data) IN
                                                        LET bad == IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {} IN
                                                          /\ /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                                                             /\ hold' = nh
                                                             /\ holders' = [v \in Values |-> IF v \in rn THEN Pinned ELSE holders[v]]
                                                             /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                                                          /\ LET r == Run(self, tj[self], (ti[self] + 1), wset[self], hold'[self], fired[self], {}, {}) IN
                                                               /\ drops' = [v \in Values |->
                                                                               IF v \in r.mk THEN (IF v \in r.dr THEN 1 ELSE 0)
                                                                               ELSE IF v \in r.dr THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                                                               /\ errs' = (       errs \cup bad
                                                                           \cup (IF \E v \in r.mk : v \in made /\ drops[v] = 0 THEN {"leak"} ELSE {})
                                                                           \cup (IF \E v \in r.dr \ r.mk : drops[v] >= 1 THEN {"double_drop"} ELSE {}))
                                                               /\ made' = (made \cup r.mk)
                                                               /\ ti' = [ti EXCEPT ![self] = r.i]
                                                               /\ wset' = [wset EXCEPT ![self] = r.w]
                                             /\ pc' = [pc EXCEPT ![self] = "OP"]
                                             /\ UNCHANGED << fired, first, 
                                                             pinned, rset, 
                                                             seen, lv, ln, cx, 
                                                             cur, lkd, ul, wv, 
                                                             ev >>
                       /\ UNCHANGED << tj, rv, commits, tc, done >>
            /\ UNCHANGED << clock, lk, ver, data, dec, pos, pubs, before >>

RD2(self) == /\ pc[self] = "RD2"
             /\ ln' = [ln EXCEPT ![self] = data[OpVar(self)]]
             /\ pc' = [pc EXCEPT ![self] = "RD3"]
             /\ UNCHANGED << clock, lk, ver, data, hold, gone, nst, drops, 
                             holders, made, tj, ti, fired, first, pinned, rv, 
                             rset, wset, seen, lv, cx, cur, lkd, ul, wv, dec, 
                             pos, pubs, commits, tc, done, before, errs, ev >>

RD3(self) == /\ pc[self] = "RD3"
             /\ IF \/ lk[OpVar(self)] \/ ver[OpVar(self)] # lv[self]
                   \/ rset[self][OpVar(self)] \notin {NONE, lv[self]}
                   THEN /\ first' = [first EXCEPT ![self] = FALSE]
                        /\ LET nr == [rset EXCEPT ![self] = [y \in Vars |-> NONE]] IN
                             LET nw == [wset EXCEPT ![self] = [y \in Vars |-> 0]] IN
                               LET d == Dying(hold, nr, nw) IN
                                 LET rn == RetireSet(d, data) IN
                                   LET pend == PendingOf(self) IN
                                     /\ cur' = [cur EXCEPT ![self] = 0]
                                     /\ cx' = [cx EXCEPT ![self] = 0]
                                     /\ drops' = [v \in Values |-> IF v \in pend THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                                     /\ errs' = (       errs \cup ({})
                                                 \cup (IF \E v \in pend : drops[v] >= 1 THEN {"double_drop"} ELSE {})
                                                 \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                                                 
                                                 \cup (IF ~FALSE /\ FALSE THEN {"hooks"} ELSE {}))
                                     /\ ev' = (ev \cup (Ev("post_retry")
                                                            \cup EvIf("reread_version", ~lk[OpVar(self)] /\ ver[OpVar(self)] = lv[self])) \cup EvIf("entry_drop", d # {}))
                                     /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                                     /\ holders' = [v \in Values |-> (IF v \in rn THEN Pinned ELSE holders[v]) \ {self}]
                                     /\ lkd' = [lkd EXCEPT ![self] = {}]
                                     /\ ln' = [ln EXCEPT ![self] = 0]
                                     /\ lv' = [lv EXCEPT ![self] = 0]
                                     /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                                     /\ pinned' = [pinned EXCEPT ![self] = FALSE]
                                     /\ rset' = nr
                                     /\ seen' = [seen EXCEPT ![self] = {}]
                                     /\ ul' = [ul EXCEPT ![self] = {}]
                                     /\ wset' = nw
                                     /\ wv' = [wv EXCEPT ![self] = 0]
                        /\ pc' = [pc EXCEPT ![self] = "TX"]
                   ELSE /\ /\ ev' = (ev \cup EvIf("reread", rset[self][OpVar(self)] # NONE))
                           /\ lv' = [lv EXCEPT ![self] = 0]
                           /\ rset' = [rset EXCEPT ![self][OpVar(self)] = lv[self]]
                        /\ pc' = [pc EXCEPT ![self] = "RD4"]
                        /\ UNCHANGED << gone, nst, drops, holders, first, 
                                        pinned, wset, seen, ln, cx, cur, lkd, 
                                        ul, wv, errs >>
             /\ UNCHANGED << clock, lk, ver, data, hold, made, tj, ti, fired, 
                             rv, dec, pos, pubs, commits, tc, done, before >>

RD4(self) == /\ pc[self] = "RD4"
             /\ LET x == OpVar(self) IN
                  LET n == ln[self] IN
                    LET s == seen[self] \cup {<<x, n>>} IN
                      /\ /\ ln' = [ln EXCEPT ![self] = 0]
                         /\ seen' = [seen EXCEPT ![self] = s]
                      /\ LET r == Run(self, tj[self], (ti[self] + 1), wset[self], hold[self], fired[self], {}, {}) IN
                           /\ drops' = [v \in Values |->
                                           IF v \in r.mk THEN (IF v \in r.dr THEN 1 ELSE 0)
                                           ELSE IF v \in r.dr THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                           /\ errs' = (       errs \cup (ReadErrs(self, s, n))
                                       \cup (IF \E v \in r.mk : v \in made /\ drops[v] = 0 THEN {"leak"} ELSE {})
                                       \cup (IF \E v \in r.dr \ r.mk : drops[v] >= 1 THEN {"double_drop"} ELSE {}))
                           /\ made' = (made \cup r.mk)
                           /\ ti' = [ti EXCEPT ![self] = r.i]
                           /\ wset' = [wset EXCEPT ![self] = r.w]
             /\ pc' = [pc EXCEPT ![self] = "OP"]
             /\ UNCHANGED << clock, lk, ver, data, hold, gone, nst, holders, 
                             tj, fired, first, pinned, rv, rset, lv, cx, cur, 
                             lkd, ul, wv, dec, pos, pubs, commits, tc, done, 
                             before, ev >>

LK1(self) == /\ pc[self] = "LK1"
             /\ IF lk[cx[self]]
                   THEN /\ IF lkd[self] = {} \/ MutKeepLocks
                              THEN /\ first' = [first EXCEPT ![self] = FALSE]
                                   /\ LET nr == [rset EXCEPT ![self] = [y \in Vars |-> NONE]] IN
                                        LET nw == [wset EXCEPT ![self] = [y \in Vars |-> 0]] IN
                                          LET d == Dying(hold, nr, nw) IN
                                            LET rn == RetireSet(d, data) IN
                                              LET pend == PendingOf(self) IN
                                                /\ cur' = [cur EXCEPT ![self] = 0]
                                                /\ cx' = [cx EXCEPT ![self] = 0]
                                                /\ drops' = [v \in Values |-> IF v \in pend THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                                                /\ errs' = (       errs \cup ({})
                                                            \cup (IF \E v \in pend : drops[v] >= 1 THEN {"double_drop"} ELSE {})
                                                            \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                                                            
                                                            \cup (IF ~FALSE /\ FALSE THEN {"hooks"} ELSE {}))
                                                /\ ev' = (ev \cup (Ev("lock_abort")) \cup EvIf("entry_drop", d # {}))
                                                /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                                                /\ holders' = [v \in Values |-> (IF v \in rn THEN Pinned ELSE holders[v]) \ {self}]
                                                /\ lkd' = [lkd EXCEPT ![self] = {}]
                                                /\ ln' = [ln EXCEPT ![self] = 0]
                                                /\ lv' = [lv EXCEPT ![self] = 0]
                                                /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                                                /\ pinned' = [pinned EXCEPT ![self] = FALSE]
                                                /\ rset' = nr
                                                /\ seen' = [seen EXCEPT ![self] = {}]
                                                /\ ul' = [ul EXCEPT ![self] = {}]
                                                /\ wset' = nw
                                                /\ wv' = [wv EXCEPT ![self] = 0]
                                   /\ pc' = [pc EXCEPT ![self] = "TX"]
                              ELSE /\ /\ ev' = (ev \cup Ev("lock_abort"))
                                      /\ ul' = [ul EXCEPT ![self] = lkd[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "UL"]
                                   /\ UNCHANGED << gone, nst, drops, holders, 
                                                   first, pinned, rset, wset, 
                                                   seen, lv, ln, cx, cur, lkd, 
                                                   wv, errs >>
                   ELSE /\ cur' = [cur EXCEPT ![self] = ver[cx[self]]]
                        /\ pc' = [pc EXCEPT ![self] = "LK2"]
                        /\ UNCHANGED << gone, nst, drops, holders, first, 
                                        pinned, rset, wset, seen, lv, ln, cx, 
                                        lkd, ul, wv, errs, ev >>
             /\ UNCHANGED << clock, lk, ver, data, hold, made, tj, ti, fired, 
                             rv, dec, pos, pubs, commits, tc, done, before >>

LK2(self) == /\ pc[self] = "LK2"
             /\ IF ~lk[cx[self]] /\ ver[cx[self]] = cur[self]
                   THEN /\ /\ lk' = [lk EXCEPT ![cx[self]] = TRUE]
                           /\ lkd' = [lkd EXCEPT ![self] = lkd[self] \cup {cx[self]}]
                        /\ IF rset[self][cx[self]] # NONE /\ cur[self] > rset[self][cx[self]]
                              THEN /\ /\ ev' = (ev \cup Ev("version_abort"))
                                      /\ ul' = [ul EXCEPT ![self] = lkd'[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "UL"]
                                   /\ cx' = cx
                              ELSE /\ IF \E y \in WVars(self) : y > cx[self]
                                         THEN /\ cx' = [cx EXCEPT ![self] = SetMin({y \in WVars(self) : y > cx[self]})]
                                              /\ pc' = [pc EXCEPT ![self] = "LK1"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "CK"]
                                              /\ cx' = cx
                                   /\ UNCHANGED << ul, ev >>
                        /\ UNCHANGED << gone, nst, drops, holders, first, 
                                        pinned, rset, wset, seen, lv, ln, cur, 
                                        wv, errs >>
                   ELSE /\ IF lk[cx[self]]
                              THEN /\ IF lkd[self] = {} \/ MutKeepLocks
                                         THEN /\ first' = [first EXCEPT ![self] = FALSE]
                                              /\ LET nr == [rset EXCEPT ![self] = [y \in Vars |-> NONE]] IN
                                                   LET nw == [wset EXCEPT ![self] = [y \in Vars |-> 0]] IN
                                                     LET d == Dying(hold, nr, nw) IN
                                                       LET rn == RetireSet(d, data) IN
                                                         LET pend == PendingOf(self) IN
                                                           /\ cur' = [cur EXCEPT ![self] = 0]
                                                           /\ cx' = [cx EXCEPT ![self] = 0]
                                                           /\ drops' = [v \in Values |-> IF v \in pend THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                                                           /\ errs' = (       errs \cup ({})
                                                                       \cup (IF \E v \in pend : drops[v] >= 1 THEN {"double_drop"} ELSE {})
                                                                       \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                                                                       
                                                                       \cup (IF ~FALSE /\ FALSE THEN {"hooks"} ELSE {}))
                                                           /\ ev' = (ev \cup (Ev("lock_abort")) \cup EvIf("entry_drop", d # {}))
                                                           /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                                                           /\ holders' = [v \in Values |-> (IF v \in rn THEN Pinned ELSE holders[v]) \ {self}]
                                                           /\ lkd' = [lkd EXCEPT ![self] = {}]
                                                           /\ ln' = [ln EXCEPT ![self] = 0]
                                                           /\ lv' = [lv EXCEPT ![self] = 0]
                                                           /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                                                           /\ pinned' = [pinned EXCEPT ![self] = FALSE]
                                                           /\ rset' = nr
                                                           /\ seen' = [seen EXCEPT ![self] = {}]
                                                           /\ ul' = [ul EXCEPT ![self] = {}]
                                                           /\ wset' = nw
                                                           /\ wv' = [wv EXCEPT ![self] = 0]
                                              /\ pc' = [pc EXCEPT ![self] = "TX"]
                                         ELSE /\ /\ ev' = (ev \cup Ev("lock_abort"))
                                                 /\ ul' = [ul EXCEPT ![self] = lkd[self]]
                                              /\ pc' = [pc EXCEPT ![self] = "UL"]
                                              /\ UNCHANGED << gone, nst, drops, 
                                                              holders, first, 
                                                              pinned, rset, 
                                                              wset, seen, lv, 
                                                              ln, cx, cur, lkd, 
                                                              wv, errs >>
                              ELSE /\ cur' = [cur EXCEPT ![self] = ver[cx[self]]]
                                   /\ pc' = [pc EXCEPT ![self] = "LK2"]
                                   /\ UNCHANGED << gone, nst, drops, holders, 
                                                   first, pinned, rset, wset, 
                                                   seen, lv, ln, cx, lkd, ul, 
                                                   wv, errs, ev >>
                        /\ lk' = lk
             /\ UNCHANGED << clock, ver, data, hold, made, tj, ti, fired, rv, 
                             dec, pos, pubs, commits, tc, done, before >>

CK(self) == /\ pc[self] = "CK"
            /\ /\ clock' = Rank(clock + 1)
               /\ cur' = [t \in Threads |-> Rank(cur[t])]
               /\ lv' = [t \in Threads |-> Rank(lv[t])]
               /\ rset' = [t \in Threads |-> [x \in Vars |->
                               IF rset[t][x] = NONE THEN NONE ELSE Rank(rset[t][x])]]
               /\ rv' = [t \in Threads |-> Rank(rv[t])]
               /\ ver' = [x \in Vars |-> Rank(ver[x])]
               /\ wv' = [t \in Threads |-> IF t = self THEN Rank(clock + 1) ELSE Rank(wv[t])]
            /\ IF MutSkipValidate \/ VVars(self) = {}
                  THEN /\ LET np == [v \in Values |-> IF \E y \in Vars : wset[self][y] = v
                                                      THEN pubs[ValVar(v)] + 1 ELSE pos[v]] IN
                            LET c == [tx |-> <<self, tj[self]>>, reads |-> seen[self],
                                      writes |-> {<<y, wset[self][y]>> : y \in WVars(self)}, before |-> before[self]] IN
                              LET nc == commits \cup {c} IN
                                LET nt == Closure(Edges(nc, np)) IN
                                  /\ commits' = nc
                                  /\ dec' = [dec EXCEPT ![self] = TRUE]
                                  /\ errs' = (       errs \cup ({})
                                              \cup (IF Cyclic(nt) THEN {"not_serializable"} ELSE {})
                                              \cup (IF \A u \in Threads \ {self} : Opaque(seen[u], before[u], nc, np, nt)
                                                    THEN {} ELSE {"opacity"}))
                                  /\ pos' = np
                                  /\ pubs' = [y \in Vars |-> IF y \in WVars(self) THEN pubs[y] + 1 ELSE pubs[y]]
                                  /\ tc' = nt
                       /\ cx' = [cx EXCEPT ![self] = SetMin(WVars(self))]
                       /\ pc' = [pc EXCEPT ![self] = "PB1"]
                  ELSE /\ cx' = [cx EXCEPT ![self] = SetMin(VVars(self))]
                       /\ pc' = [pc EXCEPT ![self] = "VA"]
                       /\ UNCHANGED << dec, pos, pubs, commits, tc, errs >>
            /\ UNCHANGED << lk, data, hold, gone, nst, drops, holders, made, 
                            tj, ti, fired, first, pinned, wset, seen, ln, lkd, 
                            ul, done, before, ev >>

VA(self) == /\ pc[self] = "VA"
            /\ IF lk[cx[self]] \/ ver[cx[self]] > rset[self][cx[self]]
                  THEN /\ /\ errs' = (errs \cup TouchVar(cx[self]))
                          /\ ev' = (ev \cup Ev("validate_abort"))
                          /\ ul' = [ul EXCEPT ![self] = lkd[self]]
                       /\ pc' = [pc EXCEPT ![self] = "UL"]
                       /\ UNCHANGED << cx, dec, pos, pubs, commits, tc >>
                  ELSE /\ IF \E y \in VVars(self) : y > cx[self]
                             THEN /\ /\ cx' = [cx EXCEPT ![self] = SetMin({y \in VVars(self) : y > cx[self]})]
                                     /\ errs' = (errs \cup TouchVar(cx[self]))
                                  /\ pc' = [pc EXCEPT ![self] = "VA"]
                                  /\ UNCHANGED << dec, pos, pubs, commits, tc >>
                             ELSE /\ LET np == [v \in Values |-> IF \E y \in Vars : wset[self][y] = v
                                                                 THEN pubs[ValVar(v)] + 1 ELSE pos[v]] IN
                                       LET c == [tx |-> <<self, tj[self]>>, reads |-> seen[self],
                                                 writes |-> {<<y, wset[self][y]>> : y \in WVars(self)}, before |-> before[self]] IN
                                         LET nc == commits \cup {c} IN
                                           LET nt == Closure(Edges(nc, np)) IN
                                             /\ commits' = nc
                                             /\ dec' = [dec EXCEPT ![self] = TRUE]
                                             /\ errs' = (       errs \cup (TouchVar(cx[self]))
                                                         \cup (IF Cyclic(nt) THEN {"not_serializable"} ELSE {})
                                                         \cup (IF \A u \in Threads \ {self} : Opaque(seen[u], before[u], nc, np, nt)
                                                               THEN {} ELSE {"opacity"}))
                                             /\ pos' = np
                                             /\ pubs' = [y \in Vars |-> IF y \in WVars(self) THEN pubs[y] + 1 ELSE pubs[y]]
                                             /\ tc' = nt
                                  /\ cx' = [cx EXCEPT ![self] = SetMin(WVars(self))]
                                  /\ pc' = [pc EXCEPT ![self] = "PB1"]
                       /\ UNCHANGED << ul, ev >>
            /\ UNCHANGED << clock, lk, ver, data, hold, gone, nst, drops, 
                            holders, made, tj, ti, fired, first, pinned, rv, 
                            rset, wset, seen, lv, ln, cur, lkd, wv, done, 
                            before >>

PB1(self) == /\ pc[self] = "PB1"
             /\ IF MutVerFirst
                   THEN /\ /\ lk' = [lk EXCEPT ![cx[self]] = FALSE]
                           /\ lkd' = [lkd EXCEPT ![self] = lkd[self] \ {cx[self]}]
                           /\ ver' = [ver EXCEPT ![cx[self]] = wv[self]]
                        /\ UNCHANGED << data, nst, drops, holders >>
                   ELSE /\ /\ data' = [data EXCEPT ![cx[self]] = wset[self][cx[self]]]
                           /\ drops' = [drops EXCEPT ![data[cx[self]]] = IF MutFreeNow THEN Min2(drops[data[cx[self]]] + 1, 2)
                                                                         ELSE drops[data[cx[self]]]]
                           /\ holders' = [holders EXCEPT ![data[cx[self]]] = Pinned]
                           /\ nst' = [nst EXCEPT ![wset[self][cx[self]]] = "live",
                                                 ![data[cx[self]]] = IF MutFreeNow THEN "freed" ELSE "retired"]
                        /\ UNCHANGED << lk, ver, lkd >>
             /\ pc' = [pc EXCEPT ![self] = "PB2"]
             /\ UNCHANGED << clock, hold, gone, made, tj, ti, fired, first, 
                             pinned, rv, rset, wset, seen, lv, ln, cx, cur, ul, 
                             wv, dec, pos, pubs, commits, tc, done, before, 
                             errs, ev >>

PB2(self) == /\ pc[self] = "PB2"
             /\ LET nw == [wset EXCEPT ![self][cx[self]] = 0] IN
                  LET old == data[cx[self]] IN
                    LET new == wset[self][cx[self]] IN
                      LET dat == IF MutVerFirst THEN [data EXCEPT ![cx[self]] = wset[self][cx[self]]] ELSE data IN
                        LET d == Dying(hold, rset, nw) IN
                          LET rn == RetireSet(d, dat) IN
                            /\ data' = dat
                            /\ drops' = [drops EXCEPT ![new] = IF MutCopy THEN Min2(@ + 1, 2) ELSE @]
                            /\ errs' =        errs
                                       \cup (IF \E v \in rn : nst[v] # "live" /\ v # new THEN {"double_drop"} ELSE {})
                            /\ ev' = (ev \cup EvIf("commit_var_drop", d # {}))
                            /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                            /\ holders' = [v \in Values |->
                                              IF v \in rn \/ (MutVerFirst /\ v = old) THEN Pinned ELSE holders[v]]
                            /\ lk' = [lk EXCEPT ![cx[self]] = IF MutVerFirst THEN lk[cx[self]] ELSE FALSE]
                            /\ lkd' = [lkd EXCEPT ![self] = lkd[self] \ {cx[self]}]
                            /\ nst' = [v \in Values |->
                                          IF v \in rn THEN "retired"
                                          ELSE IF MutVerFirst /\ v = new THEN "live"
                                          ELSE IF MutVerFirst /\ v = old THEN "retired" ELSE nst[v]]
                            /\ ver' = [ver EXCEPT ![cx[self]] = IF MutVerFirst THEN ver[cx[self]] ELSE wv[self]]
                            /\ wset' = nw
             /\ IF \E y \in WVars(self) : y > cx[self]
                   THEN /\ cx' = [cx EXCEPT ![self] = SetMin({y \in WVars(self) : y > cx[self]})]
                        /\ pc' = [pc EXCEPT ![self] = "PB1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "FIN"]
                        /\ cx' = cx
             /\ UNCHANGED << clock, hold, made, tj, ti, fired, first, pinned, 
                             rv, rset, seen, lv, ln, cur, ul, wv, dec, pos, 
                             pubs, commits, tc, done, before >>

FIN(self) == /\ pc[self] = "FIN"
             /\ /\ done' = (done \cup {<<self, tj[self]>>})
                /\ fired' = [fired EXCEPT ![self] = {}]
                /\ first' = [first EXCEPT ![self] = TRUE]
                /\ rv' = [rv EXCEPT ![self] = 0]
                /\ tj' = [tj EXCEPT ![self] = tj[self] + 1]
             /\ LET nr == [rset EXCEPT ![self] = [y \in Vars |-> NONE]] IN
                  LET nw == [wset EXCEPT ![self] = [y \in Vars |-> 0]] IN
                    LET d == Dying(hold, nr, nw) IN
                      LET rn == RetireSet(d, data) IN
                        LET pend == PendingOf(self) IN
                          /\ cur' = [cur EXCEPT ![self] = 0]
                          /\ cx' = [cx EXCEPT ![self] = 0]
                          /\ drops' = [v \in Values |-> IF v \in pend THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                          /\ errs' = (       errs \cup (IF \E y \in Vars : lk[y] /\ y \in lkd[self] THEN {"hooks"} ELSE {})
                                      \cup (IF \E v \in pend : drops[v] >= 1 THEN {"double_drop"} ELSE {})
                                      \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                                      
                                      \cup (IF ~TRUE /\ TRUE THEN {"hooks"} ELSE {}))
                          /\ ev' = (ev \cup ({}) \cup EvIf("entry_drop", d # {}))
                          /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                          /\ holders' = [v \in Values |-> (IF v \in rn THEN Pinned ELSE holders[v]) \ {self}]
                          /\ lkd' = [lkd EXCEPT ![self] = {}]
                          /\ ln' = [ln EXCEPT ![self] = 0]
                          /\ lv' = [lv EXCEPT ![self] = 0]
                          /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                          /\ pinned' = [pinned EXCEPT ![self] = FALSE]
                          /\ rset' = nr
                          /\ seen' = [seen EXCEPT ![self] = {}]
                          /\ ul' = [ul EXCEPT ![self] = {}]
                          /\ wset' = nw
                          /\ wv' = [wv EXCEPT ![self] = 0]
             /\ pc' = [pc EXCEPT ![self] = "TX"]
             /\ UNCHANGED << clock, lk, ver, data, hold, made, ti, dec, pos, 
                             pubs, commits, tc, before >>

UL(self) == /\ pc[self] = "UL"
            /\ lk' = [lk EXCEPT ![SetMin(ul[self])] = FALSE]
            /\ IF ul[self] = {SetMin(ul[self])}
                  THEN /\ first' = [first EXCEPT ![self] = FALSE]
                       /\ LET nr == [rset EXCEPT ![self] = [y \in Vars |-> NONE]] IN
                            LET nw == [wset EXCEPT ![self] = [y \in Vars |-> 0]] IN
                              LET d == Dying(hold, nr, nw) IN
                                LET rn == RetireSet(d, data) IN
                                  LET pend == PendingOf(self) IN
                                    /\ cur' = [cur EXCEPT ![self] = 0]
                                    /\ cx' = [cx EXCEPT ![self] = 0]
                                    /\ drops' = [v \in Values |-> IF v \in pend THEN Min2(drops[v] + 1, 2) ELSE drops[v]]
                                    /\ errs' = (       errs \cup ({})
                                                \cup (IF \E v \in pend : drops[v] >= 1 THEN {"double_drop"} ELSE {})
                                                \cup (IF \E v \in rn : nst[v] # "live" THEN {"double_drop"} ELSE {})
                                                
                                                \cup (IF ~FALSE /\ FALSE THEN {"hooks"} ELSE {}))
                                    /\ ev' = (ev \cup ({}) \cup EvIf("entry_drop", d # {}))
                                    /\ gone' = [y \in Vars |-> gone[y] \/ y \in d]
                                    /\ holders' = [v \in Values |-> (IF v \in rn THEN Pinned ELSE holders[v]) \ {self}]
                                    /\ lkd' = [lkd EXCEPT ![self] = {}]
                                    /\ ln' = [ln EXCEPT ![self] = 0]
                                    /\ lv' = [lv EXCEPT ![self] = 0]
                                    /\ nst' = [v \in Values |-> IF v \in rn THEN "retired" ELSE nst[v]]
                                    /\ pinned' = [pinned EXCEPT ![self] = FALSE]
                                    /\ rset' = nr
                                    /\ seen' = [seen EXCEPT ![self] = {}]
                                    /\ ul' = [ul EXCEPT ![self] = {}]
                                    /\ wset' = nw
                                    /\ wv' = [wv EXCEPT ![self] = 0]
                       /\ pc' = [pc EXCEPT ![self] = "TX"]
                  ELSE /\ /\ lkd' = [lkd EXCEPT ![self] = lkd[self] \ {SetMin(ul[self])}]
                          /\ ul' = [ul EXCEPT ![self] = ul[self] \ {SetMin(ul[self])}]
                       /\ pc' = [pc EXCEPT ![self] = "UL"]
                       /\ UNCHANGED << gone, nst, drops, holders, first, 
                                       pinned, rset, wset, seen, lv, ln, cx, 
                                       cur, wv, errs, ev >>
            /\ UNCHANGED << clock, ver, data, hold, made, tj, ti, fired, rv, 
                            dec, pos, pubs, commits, tc, done, before >>

Thread(self) == TX(self) \/ OP(self) \/ RD2(self) \/ RD3(self) \/ RD4(self)
                   \/ LK1(self) \/ LK2(self) \/ CK(self) \/ VA(self)
                   \/ PB1(self) \/ PB2(self) \/ FIN(self) \/ UL(self)

RC1 == /\ pc[0] = "RC1"
       /\ IF ~(AllDone /\ \A v \in Values : nst[v] # "retired")
             THEN /\ \E v \in {u \in Values : nst[u] = "retired" /\ holders[u] = {}}:
                       /\ drops' = [drops EXCEPT ![v] = Min2(drops[v] + 1, 2)]
                       /\ errs' = (errs \cup (IF drops[v] >= 1 THEN {"double_drop"} ELSE {}))
                       /\ nst' = [nst EXCEPT ![v] = "freed"]
                  /\ pc' = [pc EXCEPT ![0] = "RC1"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                  /\ UNCHANGED << nst, drops, errs >>
       /\ UNCHANGED << clock, lk, ver, data, hold, gone, holders, made, tj, ti, 
                       fired, first, pinned, rv, rset, wset, seen, lv, ln, cx, 
                       cur, lkd, ul, wv, dec, pos, pubs, commits, tc, done, 
                       before, ev >>

Reclaimer == RC1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Reclaimer
           \/ (\E self \in Threads: Thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 
=============================================================================
