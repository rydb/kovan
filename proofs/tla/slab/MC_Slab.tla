------------------------------ MODULE MC_Slab ------------------------------
(***************************************************************************)
(* The properties checked of Slab.tla, and the fair specification.         *)
(***************************************************************************)
EXTENDS Slab

\* A releaser between taking a block to give back and its push or count-down holds it.
InFlight(r) == IF pc[r] \in {"RR1", "RR2", "RR3", "RR4"} /\ rb[r] # NULL THEN {rb[r]} ELSE {}
\* The places of block b: a thread, a releaser giving it back, the inbox, the owner's collected
\* blocks, its chunk's free list.
Places(x) ==
    {<<"held", t>> : t \in {u \in Releasers \cup {Owner} : x \in held[u]}}
        \cup {<<"giving", r>> : r \in {u \in Releasers : x \in InFlight(u) /\ pc[u] # "RR3"}}
        \cup {<<"inbox", i>> : i \in {j \in DOMAIN inbox : inbox[j] = x}}
        \cup {<<"collected", i>> : i \in {j \in DOMAIN collected : collected[j] = x}}
        \cup (IF x \in local[ChunkOf(x)] THEN {<<"local">>} ELSE {})
        \cup (IF x \in returned THEN {<<"returned">>} ELSE {})
\* The blocks of chunk c out of it: held, being given back, or on their way through the inbox.
Out(ch) == {x \in Blocks : ChunkOf(x) = ch /\ Places(x) \ {<<"local">>, <<"returned">>} # {}}
Carved(ch) == {x \in Blocks : ChunkOf(x) = ch /\ x[2] < carved[ch]}

\* No thread touches a freed chunk or a freed inbox.
NoUseAfterFree == "uaf" \notin errs
\* Every carved block of a live chunk is in exactly one place; a block not carved yet is in none.
BlockOnce ==
    \A ch \in made \ freed : \A x \in Blocks : ChunkOf(x) = ch =>
        Cardinality(Places(x)) = IF x \in Carved(ch) THEN 1 ELSE 0
\* No block of a freed chunk is held, being given back, in the inbox or collected (its free
\* list went with its memory).
BlocksOfFreed ==
    \A x \in Blocks : ChunkOf(x) \in freed => Places(x) \subseteq {<<"local">>, <<"returned">>}
\* While the owner runs, a chunk's `used` is the count of its blocks out.
UsedRight ==
    \A ch \in made \ freed : outstanding[ch] = -1 => used[ch] = Cardinality(Out(ch))
\* Once written, a chunk's count is the count of its blocks out, which keeps it alive.
CountsRight ==
    \A ch \in made \ freed : outstanding[ch] # -1 =>
        outstanding[ch] = Cardinality(Out(ch)) /\ outstanding[ch] > 0
\* When every thread is done, every chunk and the inbox are freed.
NoLeak ==
    (\A t \in Releasers \cup {Owner} : pc[t] = "Done") => freed = made /\ inboxFreed

\* Every thread's steps taken fairly. (Termination, every thread ending, is the translation's.)
FairSpec == Spec /\ WF_vars(TheOwner) /\ \A r \in Releasers : WF_vars(Releaser(r))

\* Witnesses: each says a case never happens, so a counterexample proves the passing
\* configurations reach it.
NoRemotePushW == ver = 0 \/ inbox = <<>>
NoCountDownW == \A r \in Releasers : pc[r] # "RR4"
NoFreedByReleaserW ==
    \A r \in Releasers : ~(pc[r] = "RR4" /\ outstanding[ChunkOf(rb[r])] = 1)
NoSpareW == spare = 0
NoReuseW == \A ch \in Chunks : ~(local[ch] # {} /\ ch \in partial /\ carved[ch] = CAP /\ pc[Owner] = "OW1")
=============================================================================
