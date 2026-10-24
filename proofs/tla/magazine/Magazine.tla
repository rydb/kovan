------------------------------ MODULE Magazine ------------------------------
(***************************************************************************)
(* kovan's magazine cache (kovan/src/recycle.rs, the `recycle` feature) for *)
(* one size class, at the grain of its atomic steps.                        *)
(*                                                                          *)
(* A block is the memory of one node. Each thread keeps two magazines of    *)
(* free blocks, `loaded` and `previous`; freeing pushes on `loaded`,        *)
(* allocating pops from it, and the thread swaps the two when that helps.   *)
(* Only when neither does it go to the depot: two bounded lock-free rings   *)
(* (Vyukov's sequence-numbered ring), one of full magazines and one of      *)
(* empty ones. A thread with two full magazines hands one to the full ring  *)
(* (or, if the ring has no room, frees its blocks to the global allocator)  *)
(* and loads an empty one; a thread with two empty ones loads one from the  *)
(* full ring, or takes a block from the allocator. An exiting thread hands  *)
(* its magazines back.                                                      *)
(*                                                                          *)
(* The rings are modelled step by step: a push loads its ticket, reads the  *)
(* slot's turn word, claims the ticket with a compare-and-swap, stores the  *)
(* magazine, then publishes the turn; a pop likewise, reading the magazine  *)
(* and handing the slot to the next turn. Tickets are not wrapped (the Lean *)
(* proof covers the wrapped arithmetic). The thread-local magazine work     *)
(* between two ring operations is one step each: no other thread sees it.  *)
(*                                                                          *)
(* Each thread runs operations, each an allocation, a free of a block it   *)
(* holds, or a hand-over of a block it holds to another thread (a node     *)
(* sent along a channel, freed by whoever receives it, or by the sender    *)
(* once no thread is left to receive it), then frees every block it still  *)
(* holds and exits. A thread with a program in `Prog` runs exactly those   *)
(* operations; one without runs `Ops` operations, each any of the three.   *)
(* The threads interleave freely either way.                               *)
(*                                                                          *)
(* `Mutation` puts back one wrong rule at a time; see README.md.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Threads,    \* thread ids
    Ops,        \* operations each thread without a program runs before it drains and exits
    Prog,       \* each thread's program: a sequence of "alloc", "free" and "give", or <<>>
    ROUNDS,     \* blocks a magazine holds (32 in the code)
    SLOTS,      \* slots of each depot ring (16 in the code; at least 2)
    NBlocks,    \* blocks the layer below (the slab layer) can hand out
    BATCH,      \* blocks a refill takes from it (about 2 KiB of them in the code)
    NMags,      \* magazines that can exist at once
    Mutation    \* "none", or one wrong rule put back

\* Taking the lowest free or held block stands for taking any only while a refill orders at most
\* one block into a magazine (see Least below).
ASSUME BATCH \in {1, 2}

NULL == 0
Blocks == 1 .. NBlocks
Mags == 1 .. NMags
Full == 1
Empty == 2
Rings == {Full, Empty}
\* The turn of ticket `t`: the first ticket of its round of the ring.
Turn(t) == t - (t % SLOTS)
Range(s) == {s[i] : i \in DOMAIN s}
\* A sequence of the elements of a finite set, in some order.
SetToSeq(S) == CHOOSE q \in [1 .. Cardinality(S) -> S] : Range(q) = S
\* The lowest block of a set, and its n lowest. A step that takes some free block, or some block
\* a thread holds, takes the lowest: those blocks are named nowhere else (BlockOnce), so taking
\* another is the same step with the two blocks' names swapped, and nothing checked tells one
\* name from another (blocks are only compared for equality, and a refill orders at most one
\* block into a magazine while BATCH <= 2). So the states reached are those any choice reaches,
\* up to the names of the blocks, with none of the copies that differ only in names.
Least(S) == CHOOSE x \in S : \A y \in S : x <= y
Lowest(S, n) == {x \in S : Cardinality({y \in S : y < x}) < n}
\* The operations thread t runs, and whether it follows a program.
Scripted(t) == Len(Prog[t]) > 0
OpCount(t) == IF Scripted(t) THEN Len(Prog[t]) ELSE Ops
\* What thread t's `k`-th operation may be.
OpsAt(t, k) == IF Scripted(t) THEN {Prog[t][k]} ELSE {"alloc", "free", "give"}

\* pop_no_claim: a pop takes its ticket with a plain store instead of a compare-and-swap, so
\* two pops can take one magazine (MagOnce catches it).
MutNoClaim == Mutation = "pop_no_claim"
\* push_turn_first: a push publishes the slot's turn before it stores the magazine, so a pop can
\* read the slot's old magazine (Handover catches it).
MutTurnFirst == Mutation = "push_turn_first"
\* exit_forgets_previous: a thread's exit hands back its loaded magazine and drops the pointer to
\* the other (MagOnce catches the magazine no one has any more).
MutForget == Mutation = "exit_forgets_previous"
\* empty_to_full: an exiting thread hands an empty magazine to the full ring (FullHoldsBlocks
\* catches it).
MutEmptyToFull == Mutation = "empty_to_full"
\* swap_full_previous: a free that finds `loaded` full swaps with a full `previous` too, and
\* pushes on a full magazine (Bounded catches it).
MutSwapFull == Mutation = "swap_full_previous"
\* pop_previous_in_place: an allocation that finds `loaded` empty takes a block straight from a
\* full `previous`, leaving it neither full nor empty (PairShape catches it).
MutPopInPlace == Mutation = "pop_previous_in_place"
\* stale_ticket: a ring operation that finds its ticket already taken retries the same ticket
\* instead of reloading the current one, forever (Termination catches it).
MutStale == Mutation = "stale_ticket"
\* exit_keeps_loaded: a thread's exit hands back its previous magazine only, and the loaded one
\* stays with the exited thread (ExitReturns catches it).
MutKeep == Mutation = "exit_keeps_loaded"
\* release_leaks: a magazine the full ring has no room for has its blocks dropped instead of freed
\* to the allocator (BlockOnce catches the blocks no one has).
MutLeak == Mutation = "release_leaks"

(* --algorithm Magazine
variables
    \* the free blocks of the layer below the magazines (the slab layer, whose own protocol
    \* Slab.tla checks), and each thread's live nodes
    pool = Blocks,
    held = [t \in Threads |-> {}],
    \* each magazine's blocks, top last; the magazines no one has
    mags = [m \in Mags |-> <<>>],
    magPool = Mags,
    \* each thread's pair
    loaded = [t \in Threads |-> NULL],
    previous = [t \in Threads |-> NULL],
    \* a magazine a thread is handing to a ring, one a ring handed it, a block it is freeing
    hand = [t \in Threads |-> NULL],
    rm = [t \in Threads |-> NULL],
    fb = [t \in Threads |-> NULL],
    \* the rings: tickets, each slot's turn word and magazine
    pushAt = [r \in Rings |-> 0],
    popAt = [r \in Rings |-> 0],
    turn = [r \in Rings |-> [i \in 0 .. SLOTS - 1 |-> 0]],
    slotMag = [r \in Rings |-> [i \in 0 .. SLOTS - 1 |-> NULL]],
    \* history: the magazine each push claimed each ticket for
    ticketMag = [r \in Rings |-> <<>>],
    \* a ring operation's answer to its caller; the events the witnesses look for
    rv = [t \in Threads |-> FALSE],
    seen = {},
    \* the threads past their programs
    left = {};

define
    LenOf(m) == IF m = NULL THEN 0 ELSE Len(mags[m])
    \* The magazine slot i of ring r holds for a pop to come: published, and its ticket not yet
    \* taken by a pop.
    SlotTicket(r, i) == turn[r][i] - 1 + i
    Published(r, i) == turn[r][i] % SLOTS = 1 /\ SlotTicket(r, i) >= popAt[r]
    \* The magazine the push of a published slot's ticket stored there.
    SlotOwner(r, i) == ticketMag[r][SlotTicket(r, i) + 1]
end define;

\* ---------------------------------------------------------------- the rings
\* Hands `hand[self]` to ring `r`; answers TRUE in rv once it is published (and the hand is
\* empty), FALSE when every slot is taken (the hand still holds the magazine).
procedure RingPush(rp)
variables tp = 0, pm = NULL;
begin
RP1: \* the ticket; the magazine taken from the hand (it is the push's until published)
    tp := pushAt[rp] || pm := IF pm = NULL THEN hand[self] ELSE pm
        || hand[self] := NULL;
RP2: \* the slot's turn word
    if turn[rp][tp % SLOTS] = Turn(tp) then
        goto RP3;
    elsif turn[rp][tp % SLOTS] < Turn(tp) then
        rv[self] := FALSE || seen := seen \cup {"depot_full"} || hand[self] := pm;
        return;
    elsif MutStale then
        goto RP2;
    else
        goto RP1;
    end if;
RP3: \* the compare-and-swap of the ticket
    if pushAt[rp] = tp then
        pushAt[rp] := tp + 1 || ticketMag[rp] := Append(ticketMag[rp], pm);
    else
        tp := pushAt[rp];
        goto RP2;
    end if;
RP4: \* the magazine stored, then the turn published (the other way round under the mutation)
    if MutTurnFirst then
        turn[rp][tp % SLOTS] := Turn(tp) + 1;
    else
        slotMag[rp][tp % SLOTS] := pm;
    end if;
RP5:
    if MutTurnFirst then
        slotMag[rp][tp % SLOTS] := pm || rv[self] := TRUE;
    else
        turn[rp][tp % SLOTS] := Turn(tp) + 1 || rv[self] := TRUE;
    end if;
    return;
end procedure;

\* Takes a magazine from ring `rp` into `rm[self]`, or leaves it NULL when no slot holds one.
procedure RingPop(ro)
variables to = 0;
begin
OP1: \* the ticket
    to := popAt[ro];
OP2: \* the slot's turn word
    if turn[ro][to % SLOTS] = Turn(to) + 1 then
        goto OP3;
    elsif turn[ro][to % SLOTS] < Turn(to) + 1 then
        return;
    elsif MutStale then
        goto OP2;
    else
        goto OP1;
    end if;
OP3: \* the compare-and-swap of the ticket (a plain store under the mutation)
    if MutNoClaim then
        popAt[ro] := to + 1;
    elsif popAt[ro] = to then
        popAt[ro] := to + 1;
    else
        to := popAt[ro];
        goto OP2;
    end if;
OP4: \* the magazine read (Handover: the one the push of this ticket stored)
    rm[self] := slotMag[ro][to % SLOTS];
OP5: \* the slot handed to the next round's push
    turn[ro][to % SLOTS] := Turn(to) + SLOTS;
    return;
end procedure;

\* give_empty: keeps the empty magazine of the hand in the empty ring, or frees it.
procedure GiveEmpty()
begin
GE1:
    call RingPush(Empty);
GE2:
    if ~rv[self] then
        magPool := magPool \cup {hand[self]} || hand[self] := NULL;
    end if;
    return;
end procedure;

\* give_back (thread exit): a magazine with blocks to the full ring (its blocks to the allocator
\* when the ring has no room), an empty one to the empty ring.
procedure GiveBack()
begin
GB1:
    if LenOf(hand[self]) > 0 \/ MutEmptyToFull then
        call RingPush(Full);
    else
        call GiveEmpty();
        goto GB3;
    end if;
GB2:
    if ~rv[self] then
        pool := IF MutLeak THEN pool ELSE pool \cup Range(mags[hand[self]])
            || mags[hand[self]] := <<>>;
        call GiveEmpty();
    end if;
GB3:
    return;
end procedure;

\* ---------------------------------------------------------------- allocate and free
\* alloc_block: a block from `loaded`, from a full `previous`, from the depot's full ring, or
\* from the allocator.
procedure Alloc()
begin
AL1:
    if LenOf(loaded[self]) > 0 then
        held[self] := held[self] \cup {mags[loaded[self]][Len(mags[loaded[self]])]}
            || mags[loaded[self]] := SubSeq(mags[loaded[self]], 1, Len(mags[loaded[self]]) - 1);
        return;
    elsif LenOf(previous[self]) > 0 /\ MutPopInPlace then
        held[self] := held[self] \cup {mags[previous[self]][Len(mags[previous[self]])]}
            || mags[previous[self]] :=
                SubSeq(mags[previous[self]], 1, Len(mags[previous[self]]) - 1);
        return;
    elsif LenOf(previous[self]) > 0 then
        \* swap, and pop from the magazine swapped in
        held[self] := held[self] \cup {mags[previous[self]][Len(mags[previous[self]])]}
            || mags[previous[self]] :=
                SubSeq(mags[previous[self]], 1, Len(mags[previous[self]]) - 1)
            || loaded[self] := previous[self] || previous[self] := loaded[self];
        return;
    else
        call RingPop(Full);
    end if;
AL2:
    if rm[self] = NULL /\ loaded[self] = NULL then
        \* no full magazine: refill, an empty magazine loaded first
        call RingPop(Empty);
        goto AL2b;
    elsif rm[self] = NULL then
        goto AL2c;
    else
        \* load the full magazine and pop from it; the drained one goes to the empty ring
        held[self] := held[self] \cup {mags[rm[self]][Len(mags[rm[self]])]}
            || mags[rm[self]] := SubSeq(mags[rm[self]], 1, Len(mags[rm[self]]) - 1)
            || loaded[self] := rm[self] || rm[self] := NULL || hand[self] := loaded[self]
            || seen := seen \cup {"depot_pop"};
        if hand[self] = NULL then
            return;
        end if;
    end if;
AL3:
    call GiveEmpty();
    return;
AL2b: \* take_empty: an empty magazine from the depot, or a new one
    if rm[self] # NULL then
        loaded[self] := rm[self] || rm[self] := NULL;
    else
        with m \in magPool do
            loaded[self] := m || magPool := magPool \ {m} || mags[m] := <<>>
                || seen := seen \cup {"new_magazine"};
        end with;
    end if;
AL2c: \* refill: BATCH blocks from the layer below, one handed out, the rest into `loaded`
    await pool # {};
    with S = Lowest(pool, BATCH), x = Least(S) do
        pool := pool \ S || held[self] := held[self] \cup {x}
            || mags[loaded[self]] := mags[loaded[self]] \o SetToSeq(S \ {x})
            || seen := seen \cup {"fresh"};
    end with;
    return;
end procedure;

\* free_block: the block `fb[self]` pushed on `loaded`, on an empty `previous` (swapped in), or,
\* with a full `previous` handed to the depot (or its blocks freed when the ring is full), on an
\* empty magazine loaded from the empty ring or made new.
procedure Free()
begin
FR1:
    if loaded[self] # NULL /\ LenOf(loaded[self]) < ROUNDS then
        mags[loaded[self]] := Append(mags[loaded[self]], fb[self]) || fb[self] := NULL;
        return;
    elsif previous[self] # NULL /\ (LenOf(previous[self]) = 0 \/ MutSwapFull) then
        mags[previous[self]] := Append(mags[previous[self]], fb[self]) || fb[self] := NULL
            || loaded[self] := previous[self] || previous[self] := loaded[self];
        return;
    elsif previous[self] # NULL then
        hand[self] := previous[self] || previous[self] := NULL;
        call RingPush(Full);
    else
        goto FR3;
    end if;
FR2:
    if ~rv[self] then
        \* the depot has no room: free the magazine's blocks, swap it in empty, push on it
        pool := IF MutLeak THEN pool ELSE pool \cup Range(mags[hand[self]])
            || mags[hand[self]] := <<fb[self]>>
            || fb[self] := NULL
            || previous[self] := loaded[self] || loaded[self] := hand[self] || hand[self] := NULL;
        return;
    end if;
FR3: \* `previous` is NULL: `loaded` becomes it, and an empty magazine is loaded
    previous[self] := loaded[self] || loaded[self] := NULL;
    call RingPop(Empty);
FR4:
    if rm[self] # NULL then
        mags[rm[self]] := Append(mags[rm[self]], fb[self]) || fb[self] := NULL
            || loaded[self] := rm[self] || rm[self] := NULL;
    else
        with m \in magPool do
            mags[m] := <<fb[self]>> || fb[self] := NULL || loaded[self] := m
                || magPool := magPool \ {m} || seen := seen \cup {"new_magazine"};
        end with;
    end if;
    return;
end procedure;

\* The thread's exit: both magazines handed back (only `loaded` under the mutation).
procedure Exit()
begin
EX1:
    if loaded[self] # NULL /\ ~MutKeep then
        hand[self] := loaded[self] || loaded[self] := NULL;
        call GiveBack();
    end if;
EX2:
    if previous[self] # NULL /\ MutForget then
        previous[self] := NULL;
    elsif previous[self] # NULL then
        hand[self] := previous[self] || previous[self] := NULL;
        call GiveBack();
    end if;
EX3:
    return;
end procedure;

process Thread \in Threads
variables k = 0;
begin
TH1:
    while k < OpCount(self) do
        k := k + 1;
        either
            await "alloc" \in OpsAt(self, k);
            call Alloc();
        or
            await "free" \in OpsAt(self, k) /\ held[self] # {};
            with x = Least(held[self]) do
                held[self] := held[self] \ {x} || fb[self] := x;
            end with;
            call Free();
        or
            await "give" \in OpsAt(self, k) /\ held[self] # {};
            \* to a thread between two of its operations, or, once every other thread is past
            \* its program, freed by the thread itself
            either
                with x = Least(held[self]), u \in {v \in Threads \ {self} : pc[v] = "TH1"} do
                    held[self] := held[self] \ {x} || held[u] := held[u] \cup {x};
                end with;
            or
                await Threads \ {self} \subseteq left;
                with x = Least(held[self]) do
                    held[self] := held[self] \ {x} || fb[self] := x;
                end with;
                call Free();
            end either;
        end either;
    end while;
    left := left \cup {self};
TH2: \* free every block still held, then exit
    while held[self] # {} do
        with x = Least(held[self]) do
            held[self] := held[self] \ {x} || fb[self] := x;
        end with;
        call Free();
    end while;
TH3:
    call Exit();
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "4fcb8e1b" /\ chksum(tla) = "93b49260")
CONSTANT defaultInitValue
VARIABLES pool, held, mags, magPool, loaded, previous, hand, rm, fb, pushAt, 
          popAt, turn, slotMag, ticketMag, rv, seen, left, pc, stack

(* define statement *)
LenOf(m) == IF m = NULL THEN 0 ELSE Len(mags[m])


SlotTicket(r, i) == turn[r][i] - 1 + i
Published(r, i) == turn[r][i] % SLOTS = 1 /\ SlotTicket(r, i) >= popAt[r]

SlotOwner(r, i) == ticketMag[r][SlotTicket(r, i) + 1]

VARIABLES rp, tp, pm, ro, to, k

vars == << pool, held, mags, magPool, loaded, previous, hand, rm, fb, pushAt, 
           popAt, turn, slotMag, ticketMag, rv, seen, left, pc, stack, rp, tp, 
           pm, ro, to, k >>

ProcSet == (Threads)

Init == (* Global variables *)
        /\ pool = Blocks
        /\ held = [t \in Threads |-> {}]
        /\ mags = [m \in Mags |-> <<>>]
        /\ magPool = Mags
        /\ loaded = [t \in Threads |-> NULL]
        /\ previous = [t \in Threads |-> NULL]
        /\ hand = [t \in Threads |-> NULL]
        /\ rm = [t \in Threads |-> NULL]
        /\ fb = [t \in Threads |-> NULL]
        /\ pushAt = [r \in Rings |-> 0]
        /\ popAt = [r \in Rings |-> 0]
        /\ turn = [r \in Rings |-> [i \in 0 .. SLOTS - 1 |-> 0]]
        /\ slotMag = [r \in Rings |-> [i \in 0 .. SLOTS - 1 |-> NULL]]
        /\ ticketMag = [r \in Rings |-> <<>>]
        /\ rv = [t \in Threads |-> FALSE]
        /\ seen = {}
        /\ left = {}
        (* Procedure RingPush *)
        /\ rp = [ self \in ProcSet |-> defaultInitValue]
        /\ tp = [ self \in ProcSet |-> 0]
        /\ pm = [ self \in ProcSet |-> NULL]
        (* Procedure RingPop *)
        /\ ro = [ self \in ProcSet |-> defaultInitValue]
        /\ to = [ self \in ProcSet |-> 0]
        (* Process Thread *)
        /\ k = [self \in Threads |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "TH1"]

RP1(self) == /\ pc[self] = "RP1"
             /\ /\ hand' = [hand EXCEPT ![self] = NULL]
                /\ pm' = [pm EXCEPT ![self] = IF pm[self] = NULL THEN hand[self] ELSE pm[self]]
                /\ tp' = [tp EXCEPT ![self] = pushAt[rp[self]]]
             /\ pc' = [pc EXCEPT ![self] = "RP2"]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, rm, 
                             fb, pushAt, popAt, turn, slotMag, ticketMag, rv, 
                             seen, left, stack, rp, ro, to, k >>

RP2(self) == /\ pc[self] = "RP2"
             /\ IF turn[rp[self]][tp[self] % SLOTS] = Turn(tp[self])
                   THEN /\ pc' = [pc EXCEPT ![self] = "RP3"]
                        /\ UNCHANGED << hand, rv, seen, stack, rp, tp, pm >>
                   ELSE /\ IF turn[rp[self]][tp[self] % SLOTS] < Turn(tp[self])
                              THEN /\ /\ hand' = [hand EXCEPT ![self] = pm[self]]
                                      /\ rv' = [rv EXCEPT ![self] = FALSE]
                                      /\ seen' = (seen \cup {"depot_full"})
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ tp' = [tp EXCEPT ![self] = Head(stack[self]).tp]
                                   /\ pm' = [pm EXCEPT ![self] = Head(stack[self]).pm]
                                   /\ rp' = [rp EXCEPT ![self] = Head(stack[self]).rp]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              ELSE /\ IF MutStale
                                         THEN /\ pc' = [pc EXCEPT ![self] = "RP2"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "RP1"]
                                   /\ UNCHANGED << hand, rv, seen, stack, rp, 
                                                   tp, pm >>
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, rm, 
                             fb, pushAt, popAt, turn, slotMag, ticketMag, left, 
                             ro, to, k >>

RP3(self) == /\ pc[self] = "RP3"
             /\ IF pushAt[rp[self]] = tp[self]
                   THEN /\ /\ pushAt' = [pushAt EXCEPT ![rp[self]] = tp[self] + 1]
                           /\ ticketMag' = [ticketMag EXCEPT ![rp[self]] = Append(ticketMag[rp[self]], pm[self])]
                        /\ pc' = [pc EXCEPT ![self] = "RP4"]
                        /\ tp' = tp
                   ELSE /\ tp' = [tp EXCEPT ![self] = pushAt[rp[self]]]
                        /\ pc' = [pc EXCEPT ![self] = "RP2"]
                        /\ UNCHANGED << pushAt, ticketMag >>
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, popAt, turn, slotMag, rv, seen, left, 
                             stack, rp, pm, ro, to, k >>

RP4(self) == /\ pc[self] = "RP4"
             /\ IF MutTurnFirst
                   THEN /\ turn' = [turn EXCEPT ![rp[self]][tp[self] % SLOTS] = Turn(tp[self]) + 1]
                        /\ UNCHANGED slotMag
                   ELSE /\ slotMag' = [slotMag EXCEPT ![rp[self]][tp[self] % SLOTS] = pm[self]]
                        /\ turn' = turn
             /\ pc' = [pc EXCEPT ![self] = "RP5"]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, ticketMag, rv, seen, left, 
                             stack, rp, tp, pm, ro, to, k >>

RP5(self) == /\ pc[self] = "RP5"
             /\ IF MutTurnFirst
                   THEN /\ /\ rv' = [rv EXCEPT ![self] = TRUE]
                           /\ slotMag' = [slotMag EXCEPT ![rp[self]][tp[self] % SLOTS] = pm[self]]
                        /\ turn' = turn
                   ELSE /\ /\ rv' = [rv EXCEPT ![self] = TRUE]
                           /\ turn' = [turn EXCEPT ![rp[self]][tp[self] % SLOTS] = Turn(tp[self]) + 1]
                        /\ UNCHANGED slotMag
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ tp' = [tp EXCEPT ![self] = Head(stack[self]).tp]
             /\ pm' = [pm EXCEPT ![self] = Head(stack[self]).pm]
             /\ rp' = [rp EXCEPT ![self] = Head(stack[self]).rp]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, ticketMag, seen, left, ro, 
                             to, k >>

RingPush(self) == RP1(self) \/ RP2(self) \/ RP3(self) \/ RP4(self)
                     \/ RP5(self)

OP1(self) == /\ pc[self] = "OP1"
             /\ to' = [to EXCEPT ![self] = popAt[ro[self]]]
             /\ pc' = [pc EXCEPT ![self] = "OP2"]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, turn, slotMag, ticketMag, 
                             rv, seen, left, stack, rp, tp, pm, ro, k >>

OP2(self) == /\ pc[self] = "OP2"
             /\ IF turn[ro[self]][to[self] % SLOTS] = Turn(to[self]) + 1
                   THEN /\ pc' = [pc EXCEPT ![self] = "OP3"]
                        /\ UNCHANGED << stack, ro, to >>
                   ELSE /\ IF turn[ro[self]][to[self] % SLOTS] < Turn(to[self]) + 1
                              THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ to' = [to EXCEPT ![self] = Head(stack[self]).to]
                                   /\ ro' = [ro EXCEPT ![self] = Head(stack[self]).ro]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              ELSE /\ IF MutStale
                                         THEN /\ pc' = [pc EXCEPT ![self] = "OP2"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "OP1"]
                                   /\ UNCHANGED << stack, ro, to >>
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, turn, slotMag, ticketMag, 
                             rv, seen, left, rp, tp, pm, k >>

OP3(self) == /\ pc[self] = "OP3"
             /\ IF MutNoClaim
                   THEN /\ popAt' = [popAt EXCEPT ![ro[self]] = to[self] + 1]
                        /\ pc' = [pc EXCEPT ![self] = "OP4"]
                        /\ to' = to
                   ELSE /\ IF popAt[ro[self]] = to[self]
                              THEN /\ popAt' = [popAt EXCEPT ![ro[self]] = to[self] + 1]
                                   /\ pc' = [pc EXCEPT ![self] = "OP4"]
                                   /\ to' = to
                              ELSE /\ to' = [to EXCEPT ![self] = popAt[ro[self]]]
                                   /\ pc' = [pc EXCEPT ![self] = "OP2"]
                                   /\ popAt' = popAt
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, turn, slotMag, ticketMag, rv, 
                             seen, left, stack, rp, tp, pm, ro, k >>

OP4(self) == /\ pc[self] = "OP4"
             /\ rm' = [rm EXCEPT ![self] = slotMag[ro[self]][to[self] % SLOTS]]
             /\ pc' = [pc EXCEPT ![self] = "OP5"]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             fb, pushAt, popAt, turn, slotMag, ticketMag, rv, 
                             seen, left, stack, rp, tp, pm, ro, to, k >>

OP5(self) == /\ pc[self] = "OP5"
             /\ turn' = [turn EXCEPT ![ro[self]][to[self] % SLOTS] = Turn(to[self]) + SLOTS]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ to' = [to EXCEPT ![self] = Head(stack[self]).to]
             /\ ro' = [ro EXCEPT ![self] = Head(stack[self]).ro]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, slotMag, ticketMag, rv, 
                             seen, left, rp, tp, pm, k >>

RingPop(self) == OP1(self) \/ OP2(self) \/ OP3(self) \/ OP4(self)
                    \/ OP5(self)

GE1(self) == /\ pc[self] = "GE1"
             /\ /\ rp' = [rp EXCEPT ![self] = Empty]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "RingPush",
                                                         pc        |->  "GE2",
                                                         tp        |->  tp[self],
                                                         pm        |->  pm[self],
                                                         rp        |->  rp[self] ] >>
                                                     \o stack[self]]
             /\ tp' = [tp EXCEPT ![self] = 0]
             /\ pm' = [pm EXCEPT ![self] = NULL]
             /\ pc' = [pc EXCEPT ![self] = "RP1"]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, turn, slotMag, ticketMag, 
                             rv, seen, left, ro, to, k >>

GE2(self) == /\ pc[self] = "GE2"
             /\ IF ~rv[self]
                   THEN /\ /\ hand' = [hand EXCEPT ![self] = NULL]
                           /\ magPool' = (magPool \cup {hand[self]})
                   ELSE /\ TRUE
                        /\ UNCHANGED << magPool, hand >>
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << pool, held, mags, loaded, previous, rm, fb, 
                             pushAt, popAt, turn, slotMag, ticketMag, rv, seen, 
                             left, rp, tp, pm, ro, to, k >>

GiveEmpty(self) == GE1(self) \/ GE2(self)

GB1(self) == /\ pc[self] = "GB1"
             /\ IF LenOf(hand[self]) > 0 \/ MutEmptyToFull
                   THEN /\ /\ rp' = [rp EXCEPT ![self] = Full]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "RingPush",
                                                                    pc        |->  "GB2",
                                                                    tp        |->  tp[self],
                                                                    pm        |->  pm[self],
                                                                    rp        |->  rp[self] ] >>
                                                                \o stack[self]]
                        /\ tp' = [tp EXCEPT ![self] = 0]
                        /\ pm' = [pm EXCEPT ![self] = NULL]
                        /\ pc' = [pc EXCEPT ![self] = "RP1"]
                   ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "GiveEmpty",
                                                                 pc        |->  "GB3" ] >>
                                                             \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "GE1"]
                        /\ UNCHANGED << rp, tp, pm >>
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, turn, slotMag, ticketMag, 
                             rv, seen, left, ro, to, k >>

GB2(self) == /\ pc[self] = "GB2"
             /\ IF ~rv[self]
                   THEN /\ /\ mags' = [mags EXCEPT ![hand[self]] = <<>>]
                           /\ pool' = (IF MutLeak THEN pool ELSE pool \cup Range(mags[hand[self]]))
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "GiveEmpty",
                                                                 pc        |->  "GB3" ] >>
                                                             \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "GE1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "GB3"]
                        /\ UNCHANGED << pool, mags, stack >>
             /\ UNCHANGED << held, magPool, loaded, previous, hand, rm, fb, 
                             pushAt, popAt, turn, slotMag, ticketMag, rv, seen, 
                             left, rp, tp, pm, ro, to, k >>

GB3(self) == /\ pc[self] = "GB3"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, turn, slotMag, ticketMag, 
                             rv, seen, left, rp, tp, pm, ro, to, k >>

GiveBack(self) == GB1(self) \/ GB2(self) \/ GB3(self)

AL1(self) == /\ pc[self] = "AL1"
             /\ IF LenOf(loaded[self]) > 0
                   THEN /\ /\ held' = [held EXCEPT ![self] = held[self] \cup {mags[loaded[self]][Len(mags[loaded[self]])]}]
                           /\ mags' = [mags EXCEPT ![loaded[self]] = SubSeq(mags[loaded[self]], 1, Len(mags[loaded[self]]) - 1)]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << loaded, previous, ro, to >>
                   ELSE /\ IF LenOf(previous[self]) > 0 /\ MutPopInPlace
                              THEN /\ /\ held' = [held EXCEPT ![self] = held[self] \cup {mags[previous[self]][Len(mags[previous[self]])]}]
                                      /\ mags' = [mags EXCEPT ![previous[self]] = SubSeq(mags[previous[self]], 1, Len(mags[previous[self]]) - 1)]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED << loaded, previous, ro, to >>
                              ELSE /\ IF LenOf(previous[self]) > 0
                                         THEN /\ /\ held' = [held EXCEPT ![self] = held[self] \cup {mags[previous[self]][Len(mags[previous[self]])]}]
                                                 /\ loaded' = [loaded EXCEPT ![self] = previous[self]]
                                                 /\ mags' = [mags EXCEPT ![previous[self]] = SubSeq(mags[previous[self]], 1, Len(mags[previous[self]]) - 1)]
                                                 /\ previous' = [previous EXCEPT ![self] = loaded[self]]
                                              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                              /\ UNCHANGED << ro, to >>
                                         ELSE /\ /\ ro' = [ro EXCEPT ![self] = Full]
                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "RingPop",
                                                                                          pc        |->  "AL2",
                                                                                          to        |->  to[self],
                                                                                          ro        |->  ro[self] ] >>
                                                                                      \o stack[self]]
                                              /\ to' = [to EXCEPT ![self] = 0]
                                              /\ pc' = [pc EXCEPT ![self] = "OP1"]
                                              /\ UNCHANGED << held, mags, 
                                                              loaded, previous >>
             /\ UNCHANGED << pool, magPool, hand, rm, fb, pushAt, popAt, turn, 
                             slotMag, ticketMag, rv, seen, left, rp, tp, pm, k >>

AL2(self) == /\ pc[self] = "AL2"
             /\ IF rm[self] = NULL /\ loaded[self] = NULL
                   THEN /\ /\ ro' = [ro EXCEPT ![self] = Empty]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "RingPop",
                                                                    pc        |->  "AL2b",
                                                                    to        |->  to[self],
                                                                    ro        |->  ro[self] ] >>
                                                                \o stack[self]]
                        /\ to' = [to EXCEPT ![self] = 0]
                        /\ pc' = [pc EXCEPT ![self] = "OP1"]
                        /\ UNCHANGED << held, mags, loaded, hand, rm, seen >>
                   ELSE /\ IF rm[self] = NULL
                              THEN /\ pc' = [pc EXCEPT ![self] = "AL2c"]
                                   /\ UNCHANGED << held, mags, loaded, hand, 
                                                   rm, seen, stack >>
                              ELSE /\ /\ hand' = [hand EXCEPT ![self] = loaded[self]]
                                      /\ held' = [held EXCEPT ![self] = held[self] \cup {mags[rm[self]][Len(mags[rm[self]])]}]
                                      /\ loaded' = [loaded EXCEPT ![self] = rm[self]]
                                      /\ mags' = [mags EXCEPT ![rm[self]] = SubSeq(mags[rm[self]], 1, Len(mags[rm[self]]) - 1)]
                                      /\ rm' = [rm EXCEPT ![self] = NULL]
                                      /\ seen' = (seen \cup {"depot_pop"})
                                   /\ IF hand'[self] = NULL
                                         THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "AL3"]
                                              /\ stack' = stack
                        /\ UNCHANGED << ro, to >>
             /\ UNCHANGED << pool, magPool, previous, fb, pushAt, popAt, turn, 
                             slotMag, ticketMag, rv, left, rp, tp, pm, k >>

AL3(self) == /\ pc[self] = "AL3"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "GiveEmpty",
                                                      pc        |->  Head(stack[self]).pc ] >>
                                                  \o Tail(stack[self])]
             /\ pc' = [pc EXCEPT ![self] = "GE1"]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, turn, slotMag, ticketMag, 
                             rv, seen, left, rp, tp, pm, ro, to, k >>

AL2b(self) == /\ pc[self] = "AL2b"
              /\ IF rm[self] # NULL
                    THEN /\ /\ loaded' = [loaded EXCEPT ![self] = rm[self]]
                            /\ rm' = [rm EXCEPT ![self] = NULL]
                         /\ UNCHANGED << mags, magPool, seen >>
                    ELSE /\ \E m \in magPool:
                              /\ loaded' = [loaded EXCEPT ![self] = m]
                              /\ magPool' = magPool \ {m}
                              /\ mags' = [mags EXCEPT ![m] = <<>>]
                              /\ seen' = (seen \cup {"new_magazine"})
                         /\ rm' = rm
              /\ pc' = [pc EXCEPT ![self] = "AL2c"]
              /\ UNCHANGED << pool, held, previous, hand, fb, pushAt, popAt, 
                              turn, slotMag, ticketMag, rv, left, stack, rp, 
                              tp, pm, ro, to, k >>

AL2c(self) == /\ pc[self] = "AL2c"
              /\ pool # {}
              /\ LET S == Lowest(pool, BATCH) IN
                   LET x == Least(S) IN
                     /\ held' = [held EXCEPT ![self] = held[self] \cup {x}]
                     /\ mags' = [mags EXCEPT ![loaded[self]] = mags[loaded[self]] \o SetToSeq(S \ {x})]
                     /\ pool' = pool \ S
                     /\ seen' = (seen \cup {"fresh"})
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << magPool, loaded, previous, hand, rm, fb, pushAt, 
                              popAt, turn, slotMag, ticketMag, rv, left, rp, 
                              tp, pm, ro, to, k >>

Alloc(self) == AL1(self) \/ AL2(self) \/ AL3(self) \/ AL2b(self)
                  \/ AL2c(self)

FR1(self) == /\ pc[self] = "FR1"
             /\ IF loaded[self] # NULL /\ LenOf(loaded[self]) < ROUNDS
                   THEN /\ /\ fb' = [fb EXCEPT ![self] = NULL]
                           /\ mags' = [mags EXCEPT ![loaded[self]] = Append(mags[loaded[self]], fb[self])]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << loaded, previous, hand, rp, tp, pm >>
                   ELSE /\ IF previous[self] # NULL /\ (LenOf(previous[self]) = 0 \/ MutSwapFull)
                              THEN /\ /\ fb' = [fb EXCEPT ![self] = NULL]
                                      /\ loaded' = [loaded EXCEPT ![self] = previous[self]]
                                      /\ mags' = [mags EXCEPT ![previous[self]] = Append(mags[previous[self]], fb[self])]
                                      /\ previous' = [previous EXCEPT ![self] = loaded[self]]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                                   /\ UNCHANGED << hand, rp, tp, pm >>
                              ELSE /\ IF previous[self] # NULL
                                         THEN /\ /\ hand' = [hand EXCEPT ![self] = previous[self]]
                                                 /\ previous' = [previous EXCEPT ![self] = NULL]
                                              /\ /\ rp' = [rp EXCEPT ![self] = Full]
                                                 /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "RingPush",
                                                                                          pc        |->  "FR2",
                                                                                          tp        |->  tp[self],
                                                                                          pm        |->  pm[self],
                                                                                          rp        |->  rp[self] ] >>
                                                                                      \o stack[self]]
                                              /\ tp' = [tp EXCEPT ![self] = 0]
                                              /\ pm' = [pm EXCEPT ![self] = NULL]
                                              /\ pc' = [pc EXCEPT ![self] = "RP1"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "FR3"]
                                              /\ UNCHANGED << previous, hand, 
                                                              stack, rp, tp, 
                                                              pm >>
                                   /\ UNCHANGED << mags, loaded, fb >>
             /\ UNCHANGED << pool, held, magPool, rm, pushAt, popAt, turn, 
                             slotMag, ticketMag, rv, seen, left, ro, to, k >>

FR2(self) == /\ pc[self] = "FR2"
             /\ IF ~rv[self]
                   THEN /\ /\ fb' = [fb EXCEPT ![self] = NULL]
                           /\ hand' = [hand EXCEPT ![self] = NULL]
                           /\ loaded' = [loaded EXCEPT ![self] = hand[self]]
                           /\ mags' = [mags EXCEPT ![hand[self]] = <<fb[self]>>]
                           /\ pool' = (IF MutLeak THEN pool ELSE pool \cup Range(mags[hand[self]]))
                           /\ previous' = [previous EXCEPT ![self] = loaded[self]]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "FR3"]
                        /\ UNCHANGED << pool, mags, loaded, previous, hand, fb, 
                                        stack >>
             /\ UNCHANGED << held, magPool, rm, pushAt, popAt, turn, slotMag, 
                             ticketMag, rv, seen, left, rp, tp, pm, ro, to, k >>

FR3(self) == /\ pc[self] = "FR3"
             /\ /\ loaded' = [loaded EXCEPT ![self] = NULL]
                /\ previous' = [previous EXCEPT ![self] = loaded[self]]
             /\ /\ ro' = [ro EXCEPT ![self] = Empty]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "RingPop",
                                                         pc        |->  "FR4",
                                                         to        |->  to[self],
                                                         ro        |->  ro[self] ] >>
                                                     \o stack[self]]
             /\ to' = [to EXCEPT ![self] = 0]
             /\ pc' = [pc EXCEPT ![self] = "OP1"]
             /\ UNCHANGED << pool, held, mags, magPool, hand, rm, fb, pushAt, 
                             popAt, turn, slotMag, ticketMag, rv, seen, left, 
                             rp, tp, pm, k >>

FR4(self) == /\ pc[self] = "FR4"
             /\ IF rm[self] # NULL
                   THEN /\ /\ fb' = [fb EXCEPT ![self] = NULL]
                           /\ loaded' = [loaded EXCEPT ![self] = rm[self]]
                           /\ mags' = [mags EXCEPT ![rm[self]] = Append(mags[rm[self]], fb[self])]
                           /\ rm' = [rm EXCEPT ![self] = NULL]
                        /\ UNCHANGED << magPool, seen >>
                   ELSE /\ \E m \in magPool:
                             /\ fb' = [fb EXCEPT ![self] = NULL]
                             /\ loaded' = [loaded EXCEPT ![self] = m]
                             /\ magPool' = magPool \ {m}
                             /\ mags' = [mags EXCEPT ![m] = <<fb[self]>>]
                             /\ seen' = (seen \cup {"new_magazine"})
                        /\ rm' = rm
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << pool, held, previous, hand, pushAt, popAt, turn, 
                             slotMag, ticketMag, rv, left, rp, tp, pm, ro, to, 
                             k >>

Free(self) == FR1(self) \/ FR2(self) \/ FR3(self) \/ FR4(self)

EX1(self) == /\ pc[self] = "EX1"
             /\ IF loaded[self] # NULL /\ ~MutKeep
                   THEN /\ /\ hand' = [hand EXCEPT ![self] = loaded[self]]
                           /\ loaded' = [loaded EXCEPT ![self] = NULL]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "GiveBack",
                                                                 pc        |->  "EX2" ] >>
                                                             \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "GB1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "EX2"]
                        /\ UNCHANGED << loaded, hand, stack >>
             /\ UNCHANGED << pool, held, mags, magPool, previous, rm, fb, 
                             pushAt, popAt, turn, slotMag, ticketMag, rv, seen, 
                             left, rp, tp, pm, ro, to, k >>

EX2(self) == /\ pc[self] = "EX2"
             /\ IF previous[self] # NULL /\ MutForget
                   THEN /\ previous' = [previous EXCEPT ![self] = NULL]
                        /\ pc' = [pc EXCEPT ![self] = "EX3"]
                        /\ UNCHANGED << hand, stack >>
                   ELSE /\ IF previous[self] # NULL
                              THEN /\ /\ hand' = [hand EXCEPT ![self] = previous[self]]
                                      /\ previous' = [previous EXCEPT ![self] = NULL]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "GiveBack",
                                                                            pc        |->  "EX3" ] >>
                                                                        \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "GB1"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "EX3"]
                                   /\ UNCHANGED << previous, hand, stack >>
             /\ UNCHANGED << pool, held, mags, magPool, loaded, rm, fb, pushAt, 
                             popAt, turn, slotMag, ticketMag, rv, seen, left, 
                             rp, tp, pm, ro, to, k >>

EX3(self) == /\ pc[self] = "EX3"
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, turn, slotMag, ticketMag, 
                             rv, seen, left, rp, tp, pm, ro, to, k >>

Exit(self) == EX1(self) \/ EX2(self) \/ EX3(self)

TH1(self) == /\ pc[self] = "TH1"
             /\ IF k[self] < OpCount(self)
                   THEN /\ k' = [k EXCEPT ![self] = k[self] + 1]
                        /\ \/ /\ "alloc" \in OpsAt(self, k'[self])
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Alloc",
                                                                       pc        |->  "TH1" ] >>
                                                                   \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "AL1"]
                              /\ UNCHANGED <<held, fb>>
                           \/ /\ "free" \in OpsAt(self, k'[self]) /\ held[self] # {}
                              /\ LET x == Least(held[self]) IN
                                   /\ fb' = [fb EXCEPT ![self] = x]
                                   /\ held' = [held EXCEPT ![self] = held[self] \ {x}]
                              /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Free",
                                                                       pc        |->  "TH1" ] >>
                                                                   \o stack[self]]
                              /\ pc' = [pc EXCEPT ![self] = "FR1"]
                           \/ /\ "give" \in OpsAt(self, k'[self]) /\ held[self] # {}
                              /\ \/ /\ LET x == Least(held[self]) IN
                                         \E u \in {v \in Threads \ {self} : pc[v] = "TH1"}:
                                           held' = [held EXCEPT ![self] = held[self] \ {x},
                                                                ![u] = held[u] \cup {x}]
                                    /\ pc' = [pc EXCEPT ![self] = "TH1"]
                                    /\ UNCHANGED <<fb, stack>>
                                 \/ /\ Threads \ {self} \subseteq left
                                    /\ LET x == Least(held[self]) IN
                                         /\ fb' = [fb EXCEPT ![self] = x]
                                         /\ held' = [held EXCEPT ![self] = held[self] \ {x}]
                                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Free",
                                                                             pc        |->  "TH1" ] >>
                                                                         \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "FR1"]
                        /\ left' = left
                   ELSE /\ left' = (left \cup {self})
                        /\ pc' = [pc EXCEPT ![self] = "TH2"]
                        /\ UNCHANGED << held, fb, stack, k >>
             /\ UNCHANGED << pool, mags, magPool, loaded, previous, hand, rm, 
                             pushAt, popAt, turn, slotMag, ticketMag, rv, seen, 
                             rp, tp, pm, ro, to >>

TH2(self) == /\ pc[self] = "TH2"
             /\ IF held[self] # {}
                   THEN /\ LET x == Least(held[self]) IN
                             /\ fb' = [fb EXCEPT ![self] = x]
                             /\ held' = [held EXCEPT ![self] = held[self] \ {x}]
                        /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Free",
                                                                 pc        |->  "TH2" ] >>
                                                             \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "FR1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "TH3"]
                        /\ UNCHANGED << held, fb, stack >>
             /\ UNCHANGED << pool, mags, magPool, loaded, previous, hand, rm, 
                             pushAt, popAt, turn, slotMag, ticketMag, rv, seen, 
                             left, rp, tp, pm, ro, to, k >>

TH3(self) == /\ pc[self] = "TH3"
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Exit",
                                                      pc        |->  "Done" ] >>
                                                  \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "EX1"]
             /\ UNCHANGED << pool, held, mags, magPool, loaded, previous, hand, 
                             rm, fb, pushAt, popAt, turn, slotMag, ticketMag, 
                             rv, seen, left, rp, tp, pm, ro, to, k >>

Thread(self) == TH1(self) \/ TH2(self) \/ TH3(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet:  \/ RingPush(self) \/ RingPop(self)
                               \/ GiveEmpty(self) \/ GiveBack(self)
                               \/ Alloc(self) \/ Free(self) \/ Exit(self))
           \/ (\E self \in Threads: Thread(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
