------------------------------ MODULE MC_Atom ------------------------------
(***************************************************************************)
(* The properties checked of Atom.tla, the threads' programs, and the fair *)
(* specification.                                                          *)
(***************************************************************************)
EXTENDS Atom

\* A pointer is valid while its address holds the node it named and that node's value is not
\* dropped (the value's own memory, a String's buffer say, lives as long as the value).
Valid(p) == p = NOP \/ (node[p[1]].st # "free" /\ node[p[1]].ver = p[2] /\ vst[p[2]] # "dropped")

\* No thread dereferences a node freed (or its address reused) or a value dropped: not through an
\* AtomGuard, not swap's read of the old node, not rcu's closure, not an AtomGuard on its way to
\* another thread, not a Removed.
NoUseAfterFree ==
    /\ \A t \in Threads : \A p \in Held(t) : Valid(p)
    /\ Valid(mailbox)
    /\ \A t \in Threads : rem[t] # NOREM => vst[rem[t].v] # "dropped"

\* No value is dropped twice, no node freed twice.
DropOnce == errs \cap {"double_drop", "double_free"} = {}

\* When every thread is done, nothing is lost: every node is free, retired (kovan frees it once
\* its sections end) or the atom's own; every value is dropped, or owned by such a node.
NoLeak ==
    AllDone =>
        /\ \A a \in Addrs : node[a].st = "live" => alive /\ cell = a
        /\ \A t \in Threads : rem[t] = NOREM
        /\ \A v \in Vals : vst[v] = "live" =>
            \E a \in Addrs :
                /\ node[a].st \in {"live", "retired"} /\ node[a].own /\ OwnedVal(node[a]) = v
                /\ (node[a].st = "retired" => node[a].kind = "drop")

\* A Removed and every AtomGuard of the same value reach one object: the value in the node the
\* guards loaded, not a copy of it (the code before 15ae2c4 handed back a copy).
OneObject ==
    \A t, u \in Threads :
        rem[t] # NOREM =>
            \A p \in {ag[u], cg[u]} :
                (p # NOP /\ p[2] = rem[t].v) => (~rem[t].copy /\ p[1] = rem[t].a)

\* Every value a load answers, swap or take returns, or rcu's closure reads, was the atom's at
\* some moment of the call.
Linearizable == "lin" \notin errs

\* compare_and_swap answers Ok exactly when the atom held `current`'s node at its compare-and-swap,
\* and Err only when it did not at the step that told it so.
CasExact == "cas_exact" \notin errs

\* An rcu's compare-and-swap replaces the node its closure read.
RcuApplies == "rcu_applies" \notin errs

\* An rcu attempt fails only when another thread's write took effect since its load: every retry
\* is paid for by a write that succeeded, so the threads together make progress.
LockFree == "lockfree" \notin errs

\* Eventually nothing stays retired: every node retired is freed (FairSpec).
Reclaimed == <>[](\A a \in Addrs : node[a].st # "retired")

\* Every thread's steps and the reclamation's taken fairly. (Termination, every process ending,
\* is the translation's.)
FairSpec == Spec /\ WF_vars(Reclaimer) /\ \A t \in Threads : WF_vars(Thread(t))

\* Witnesses: each says a case never happens, so a counterexample proves the passing
\* configurations reach it. A configuration records only the event its witness names (`Wit`).
\* kovan frees a retired node; an allocation takes a freed address again.
NoFreeW == "free" \notin said
NoReuseW == "reuse" \notin said
\* A retire leaves out a live section whose published epoch is below the node's birth (the
\* birth filter acts); a protected load raises its section's published epoch.
NoSkipW == "skip" \notin said
NoRaiseW == "raise" \notin said
\* A write retires a node a reader's AtomGuard holds, or the node the AtomGuard a
\* compare_and_swap returned holds.
NoHeldW == "held" \notin said
NoOkHeldW == "ok_held" \notin said
\* A Removed's drop retires its node while a reader still holds it.
NoRemovedHeldW == "removed_held" \notin said
\* A Removed is dropped after the atom is gone.
NoLateRemovedW == "late_removed" \notin said
\* One rcu call retries twice: the retries are bounded by the other threads' writes, not by a
\* number of its own steps.
NoRcuRetry2W == "rcu_retry2" \notin said
\* An rcu retries; compare_and_swap answers Err at its compare with `current`, and at its
\* compare-and-swap after a write between the two.
NoRcuRetryW == "rcu_retry" \notin said
NoCasErrLoadW == "cas_err_load" \notin said
NoCasRaceW == "cas_err_race" \notin said
\* AtomOption::load answers None; is_none answers true.
NoNoneW == "none" \notin said
NoIsNoneW == "is_none" \notin said

\* ---------------------------------------------------------------- programs
\* "load" keeps an AtomGuard (AtomMap::load the same), "drop" drops it; "store", "swap", "take",
\* "store_none", "is_none", "rcu" are the methods; "cas" is compare_and_swap with the thread's
\* AtomGuard as `current`, and "dropc" drops the AtomGuard its Ok returned; "dropr" drops the
\* Removed (retiring its node), "unchecked" takes it apart with into_inner_unchecked; "into_inner" and "dropatom" end
\* the atom; "send" and "recv" move an AtomGuard to another thread (guard_send only).

\* A reader loads twice across two stores and a swap whose Removed is dropped.
ProgStore == (1 :> <<"load", "drop", "load", "drop">>) @@ (2 :> <<"store", "store">>)
    @@ (3 :> <<"swap", "dropr">>)
\* A compare_and_swap against the value a guard holds races an rcu and a store; the guard it
\* returns outlives `current` and a nested load under it.
ProgCas == (1 :> <<"load", "cas", "drop", "load", "dropc", "drop">>) @@ (2 :> <<"rcu">>)
    @@ (3 :> <<"store">>)
\* Two threads run two rcus each, racing each other, with a reader.
ProgRcu == (1 :> <<"rcu", "rcu">>) @@ (2 :> <<"rcu", "rcu">>) @@ (3 :> <<"load", "drop">>)
\* Two compare_and_swaps against the same value race each other and a store.
ProgCas2 == (1 :> <<"load", "cas", "dropc", "drop">>) @@ (2 :> <<"load", "cas", "dropc", "drop">>)
    @@ (3 :> <<"store">>)
\* An AtomOption that starts empty: a store and two takes whose Removeds are dropped, a store_none
\* and a store race a reader that loads twice and asks is_none.
ProgOpt == (1 :> <<"store", "take", "dropr">>)
    @@ (2 :> <<"load", "drop", "is_none", "take", "dropr", "load", "drop">>)
    @@ (3 :> <<"store_none", "store">>)
\* A compare_and_swap, a swap whose Removed is dropped, and an rcu race each other.
ProgMix == (1 :> <<"load", "cas", "dropc", "drop">>) @@ (2 :> <<"swap", "dropr">>) @@ (3 :> <<"rcu">>)
\* The atom dropped once the others are done, its last value with it, and a Removed of it dropped
\* after it.
ProgEnd == (1 :> <<"swap", "dropatom", "dropr">>) @@ (2 :> <<"load", "drop", "rcu">>)
    @@ (3 :> <<"store", "load", "drop">>)
\* into_inner once the others are done; a Removed taken apart with into_inner_unchecked once no
\* reader can reach its value.
ProgInner == (1 :> <<"load", "cas", "dropc", "drop">>) @@ (2 :> <<"store", "into_inner">>)
    @@ (3 :> <<"swap", "unchecked">>)
\* Two rcus, a swap and the drop of its Removed, then the atom's drop: every operation ends, every
\* node is freed.
ProgLive == (1 :> <<"rcu">>) @@ (2 :> <<"rcu">>) @@ (3 :> <<"swap", "dropr", "dropatom">>)
\* (guard_send) an AtomGuard dropped on a thread that holds one of its own, under two stores.
ProgSend == (1 :> <<"load", "send">>) @@ (2 :> <<"load", "recv", "drop">>)
    @@ (3 :> <<"store", "store">>)
\* (guard_send) an AtomGuard dropped on a thread with no guard: its own thread stays pinned.
ProgSendIdle == (1 :> <<"load", "send">>) @@ (2 :> <<"recv">>) @@ (3 :> <<"store">>)
\* (cas_load_unprotected) a compare_and_swap after a retire in the same section moved the epoch,
\* its guard then held across a store.
ProgCasOk == (1 :> <<"swap", "load", "dropr", "cas", "dropc", "drop">>) @@ (2 :> <<"store">>)
\* (load_unprotected) a compare_and_swap against a guard that does not protect its node, under
\* four stores.
ProgAba == (1 :> <<"load", "cas", "dropc", "drop">>)
    @@ (2 :> <<"store", "store", "store", "store">>)
=============================================================================
