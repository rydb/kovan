---------------------------- MODULE MC_Magazine ----------------------------
(***************************************************************************)
(* The properties checked of Magazine.tla, and the fair specification.     *)
(***************************************************************************)
EXTENDS Magazine

\* A push owns its magazine until the step that publishes the slot's turn: the last step, or
\* under push_turn_first the one before it.
PushOwns(t) ==
    pc[t] \in {"RP1", "RP2", "RP3", "RP4"} \/ (pc[t] = "RP5" /\ ~MutTurnFirst)
\* The magazines a thread has: its pair, one in its hand, one a ring handed it, one it is pushing
\* and has not published, and the one of the ticket it has claimed in a ring and not read yet.
OwnedBy(t) ==
    {m \in {loaded[t], previous[t], hand[t], rm[t]} : m # NULL}
        \cup (IF PushOwns(t) /\ pm[t] # NULL THEN {pm[t]} ELSE {})
        \cup (IF pc[t] = "OP4" THEN {ticketMag[ro[t]][to[t] + 1]} ELSE {})
\* How many places hold magazine `m`: a thread, or a published slot of a ring.
Holders(m) ==
    Cardinality({t \in Threads : m \in OwnedBy(t)})
        + Cardinality({<<r, i>> \in Rings \X (0 .. SLOTS - 1) : Published(r, i) /\ SlotOwner(r, i) = m})
\* A thread can hold one magazine in two roles at once only by a bug: count roles too.
Roles(m) ==
    Cardinality({t \in Threads : loaded[t] = m}) + Cardinality({t \in Threads : previous[t] = m})
        + Cardinality({t \in Threads : hand[t] = m}) + Cardinality({t \in Threads : rm[t] = m})

\* Every magazine is in exactly one place, or is one no one has (then empty).
MagOnce ==
    \A m \in Mags :
        IF m \in magPool THEN Holders(m) = 0 /\ Roles(m) = 0 /\ mags[m] = <<>>
        ELSE Holders(m) = 1 /\ Roles(m) <= 1

\* The places of block `b`: the allocator, a thread's live nodes, a free in progress, a position
\* of a magazine someone has.
Places(b) ==
    (IF b \in pool THEN {<<"pool">>} ELSE {})
        \cup {<<"held", t>> : t \in {u \in Threads : b \in held[u]}}
        \cup {<<"freeing", t>> : t \in {u \in Threads : fb[u] = b}}
        \cup {<<"mag", m, i>> : <<m, i>> \in {<<n, j>> \in (Mags \ magPool) \X (1 .. ROUNDS + 1) :
                                                  j \in DOMAIN mags[n] /\ mags[n][j] = b}}
\* Every block is in exactly one place: never handed to two owners, never lost.
BlockOnce == \A b \in Blocks : Cardinality(Places(b)) = 1

\* A pop about to read its slot finds there the magazine the push of its ticket stored.
Handover ==
    \A t \in Threads : pc[t] = "OP4" => slotMag[ro[t]][to[t] % SLOTS] = ticketMag[ro[t]][to[t] + 1]

\* The full ring holds only magazines with blocks.
FullHoldsBlocks ==
    \A i \in 0 .. SLOTS - 1 : Published(Full, i) => Len(mags[SlotOwner(Full, i)]) > 0

\* No magazine holds more than ROUNDS blocks, and no thread more than its pair and one in hand.
Bounded ==
    /\ \A m \in Mags : Len(mags[m]) <= ROUNDS
    /\ \A t \in Threads : Cardinality(OwnedBy(t)) <= 3

\* Between two operations a thread's pair is as the code says: `loaded` is NULL only while
\* `previous` is, and `previous` is NULL, empty or full.
PairShape ==
    \A t \in Threads : pc[t] \in {"TH1", "TH2"} =>
        /\ (loaded[t] = NULL => previous[t] = NULL)
        /\ (previous[t] = NULL \/ LenOf(previous[t]) \in {0, ROUNDS})

\* When every thread has exited, no thread keeps a magazine or a block: what the cache keeps is
\* in the depot.
ExitReturns ==
    (\A t \in Threads : pc[t] = "Done") =>
        \A t \in Threads : OwnedBy(t) = {} /\ held[t] = {} /\ fb[t] = NULL

\* The threads' programs: "a" allocates, "f" frees a block the thread holds, "g" hands one to a
\* running thread, or frees it once every other thread is past its program. A thread drains and
\* exits after its program.
NoProg == [t \in Threads |-> <<>>]
\* Thread 1 runs any operations; thread 2 allocates, then frees.
ProgOpen == (1 :> <<>>) @@ (2 :> <<"alloc", "free">>)
\* One thread fills the depot (its third free hands a full magazine over, its exit two more)
\* while two others allocate, so two pops can race for one magazine.
ProgFill3 == (1 :> <<"alloc", "alloc", "alloc", "free", "free", "free">>)
    @@ (2 :> <<"alloc">>) @@ (3 :> <<"alloc">>)
\* One thread fills the depot at its exit (one full magazine) while two others allocate, so the two
\* pops race for that one magazine.
ProgRace == (1 :> <<"alloc", "free">>) @@ (2 :> <<"alloc">>) @@ (3 :> <<"alloc">>)
\* One thread fills the depot while another allocates from it.
ProgFill2 == (1 :> <<"alloc", "alloc", "alloc", "free", "free", "free">>) @@ (2 :> <<"alloc">>)
\* A producer hands its nodes to a consumer, which frees them: blocks cross threads.
ProgTrade == (1 :> <<"alloc", "alloc", "give", "give">>) @@ (2 :> <<"alloc", "alloc">>)
\* Two-block magazines: partial magazines, and swaps both ways.
ProgRounds == (1 :> <<"alloc", "alloc", "alloc", "free", "free", "free", "alloc">>)
    @@ (2 :> <<"alloc", "alloc", "free", "free", "alloc", "alloc">>)
\* Two threads that exit with three full magazines between them, racing for the full ring's
\* tickets, one more than its two slots hold.
ProgExits == (1 :> <<"alloc", "alloc", "free", "free">>) @@ (2 :> <<"alloc", "free">>)
\* One thread going round both rings more than once.
ProgCycle == 1 :> <<"alloc", "alloc", "alloc", "free", "free", "free", "alloc", "alloc", "alloc",
    "free", "free", "free">>
\* One thread: two frees (loaded and previous full), three frees, a free and an allocation, and
\* four of each then three allocations with two-block magazines.
ProgTwoFrees == 1 :> <<"alloc", "alloc", "free", "free">>
ProgThreeFrees == 1 :> <<"alloc", "alloc", "alloc", "free", "free", "free">>
ProgFreeAlloc == 1 :> <<"alloc", "free", "alloc">>
ProgDeep == 1 :> <<"alloc", "alloc", "alloc", "alloc", "free", "free", "free", "free",
    "alloc", "alloc", "alloc">>
\* A thread that ends with an empty magazine: its last block goes to another thread.
ProgEmptyExit == (1 :> <<"alloc", "free", "alloc", "give">>) @@ (2 :> <<"alloc", "alloc", "alloc">>)

\* Every thread's steps taken fairly. (Termination, every thread ending, is the translation's.)
FairSpec == Spec /\ \A t \in Threads : WF_vars(Thread(t) \/ Alloc(t) \/ Free(t) \/ Exit(t)
    \/ GiveBack(t) \/ GiveEmpty(t) \/ RingPush(t) \/ RingPop(t))

\* Witnesses: each says a case never happens, so a counterexample proves the passing
\* configurations reach it.
NoDepotPopW == "depot_pop" \notin seen
NoDepotFullW == "depot_full" \notin seen
NoFreshW == "fresh" \notin seen
NoNewMagazineW == "new_magazine" \notin seen
NoWrapW == \A r \in Rings : pushAt[r] <= SLOTS
NoExitToDepotW ==
    (\A t \in Threads : pc[t] = "Done") => \A i \in 0 .. SLOTS - 1 : ~Published(Full, i)
=============================================================================
