------------------------------- MODULE MC_Stm -------------------------------
(***************************************************************************)
(* The properties checked of Stm.tla, the threads' programs and the fair   *)
(* specification.                                                           *)
(***************************************************************************)
EXTENDS Stm

\* No step reads a freed node or a dropped value, and none touches a variable after it was freed.
NoUseAfterFree == "uaf" \notin errs
\* No value is dropped twice (and no node retired twice).
DropOnce == "double_drop" \notin errs
\* The committed transactions are serializable, in an order that keeps real time: their
\* dependencies (a read of another's write, an overwrite of another's write or of a value it
\* read, a start after another returned) form no cycle.
Serializable == "not_serializable" \notin errs
\* Every attempt, committed, running or aborted, reads a state the committed transactions can be
\* serialized around: placed among them as a read-only transaction, it closes no cycle.
Opacity == "opacity" \notin errs
\* No attempt sees one write of a commit and, for another variable that commit wrote, an older
\* value: a commit's writes are seen all or none.
AllOrNone == "torn" \notin errs
\* The rollback hooks never run for a transaction that committed, and the commit hooks run
\* after every lock is released.
HooksRight == "hooks" \notin errs
\* A variable's lock bit is set exactly while one committer holds it.
LockOwned ==
    /\ \A x \in Vars : lk[x] <=> \E t \in Threads : x \in lkd[t]
    /\ \A t, u \in Threads : t # u => lkd[t] \cap lkd[u] = {}
\* When every thread and the reclamation are done, every variable was freed, every node freed,
\* and every value made dropped exactly once; and no value was made again before its earlier
\* making was dropped.
AllEnded == \A p \in ProcSet : pc[p] = "Done"
NoLeak ==
    /\ "leak" \notin errs
    /\ AllEnded =>
        /\ \A x \in Vars : gone[x]
        /\ \A v \in Values : nst[v] \in {"none", "freed"}
        /\ \A v \in made \cup InitVals : drops[v] = 1

\* Once every other thread is done, a thread finishes: a transaction running alone commits.
SoloEnds == \A t \in Threads : (\A u \in Threads \ {t} : pc[u] = "Done") ~> (pc[t] = "Done")

\* Every thread's steps and the reclamation's taken fairly. (Termination, every process ending,
\* is the translation's.)
FairSpec == Spec /\ WF_vars(Reclaimer) /\ \A t \in Threads : WF_vars(Thread(t))

\* The operations of a closure.
R(x) == <<"r", x>>
W(x) == <<"w", x>>
D(x) == <<"d", x>>
Retry == <<"retry">>

\* A transfer between two variables; a read of both, then an increment of the second: a
\* reader against a commit of two variables, two commits racing for a lock.
ProgTransfer ==
    (1 :> << <<R(1), R(2), W(1), W(2)>> >>)
        @@ (2 :> << <<R(1), R(2)>>, <<R(2), W(2)>> >>)
\* ProgTransfer and a third thread incrementing the first variable: three commits racing.
ProgTransfer3 == ProgTransfer @@ (3 :> << <<R(1), W(1)>> >>)
\* Each thread reads what the other writes (the write skew's shape): each commit validates a
\* variable the other may hold locked.
ProgCross == (1 :> << <<R(1), W(2)>> >>) @@ (2 :> << <<R(2), W(1)>> >>)
\* ProgCross and a reader of both variables.
ProgCrossRead == ProgCross @@ (3 :> << <<R(1), R(2)>> >>)
\* Three increments of one variable.
ProgIncr3 ==
    (1 :> << <<R(1), W(1)>> >>) @@ (2 :> << <<R(1), W(1)>> >>) @@ (3 :> << <<R(1), W(1)>> >>)
\* The drops of tests/drops.rs and more: a store replaced by a second one, a retry that rolls
\* both back; a variable read, its handle dropped, then validated by the commit (the read entry
\* keeps it alive); a variable stored to, its handle dropped, so the commit's own reference is
\* the last (the commit drops it); while another thread reads the first variable, then
\* increments it.
ProgDrops ==
    (1 :> << <<W(1), W(1), Retry>>, <<R(2), D(2), W(1)>>, <<W(3), D(3)>> >>)
        @@ (2 :> << <<R(1)>>, <<R(1), W(1)>> >>)
\* A variable read twice in one transaction that no other thread writes, while another variable
\* is written.
ProgRereadQuiet ==
    (1 :> << <<R(1), R(2), R(1), W(2)>> >>) @@ (2 :> << <<R(2), W(2)>>, <<R(1), R(2)>> >>)
\* Two rounds of transactions on two variables by two threads: commits that follow commits.
ProgRounds ==
    (1 :> << <<R(1), W(1), W(2)>>, <<R(2), R(1)>> >>)
        @@ (2 :> << <<R(2), W(2)>>, <<R(1), W(1)>> >>)
\* Two commits of one variable by one thread (tests/drops.rs, a_committed_value_is_dropped_once).
ProgCommitted == 1 :> << <<W(1)>>, <<W(1)>> >>
\* A variable read twice while another thread writes it: read-only, an update, and a read of a
\* second variable the writer also writes in between (the shortcut f691cc5 removed let each of
\* these see the commit half: two values of x, or x new with y old).
ProgReread == (1 :> << <<R(1), R(1)>> >>) @@ (2 :> << <<W(1)>> >>)
ProgRereadUpdate == (1 :> << <<R(1), R(1), W(2)>> >>) @@ (2 :> << <<W(1)>> >>)
ProgRereadTorn == (1 :> << <<R(1), R(2), R(1)>> >>) @@ (2 :> << <<W(1), W(2)>> >>)

\* Witnesses: each says a case never happens, so a counterexample proves the passing
\* configurations reach it. The events are recorded only for the configuration's `Witness`.
NoLockAbortW == "lock_abort" \notin ev
NoVersionAbortW == "version_abort" \notin ev
NoValidateAbortW == "validate_abort" \notin ev
NoReadRetryW == "read_retry" \notin ev
NoPostRetryW == "post_retry" \notin ev
NoRereadW == "reread" \notin ev
NoRereadRetryW == "reread_retry" \notin ev
\* A repeat read finds its variable unlocked and stable but at another version than its first read
\* recorded (the check `first.version != version`).
NoRereadVersionW == "reread_version" \notin ev
NoEntryDropW == "entry_drop" \notin ev
NoCommitDropW == "commit_var_drop" \notin ev
\* A node is retired while a thread that loaded it is still pinned.
NoGuardedRetireW ==
    \A v \in Values : nst[v] = "retired" =>
        ~\E t \in holders[v] : ln[t] = v \/ \E p \in seen[t] : p[2] = v
\* A node is freed while a thread still runs.
NoEarlyFreeW == AllDone \/ \A v \in Values : nst[v] # "freed"
=============================================================================
