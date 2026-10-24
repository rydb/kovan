------------------------------ MODULE SegQueue ------------------------------
(***************************************************************************)
(* kovan_queue::SegQueue (kovan-queue/src/seg_queue.rs) at the grain of     *)
(* its atomic steps.                                                        *)
(*                                                                          *)
(* The queue is a linked list of segments of SEG cells. Each end is a claim *)
(* word (a segment id and an index) and a segment pointer. A push claims a  *)
(* cell with one fetch-add on the tail word and publishes its value with    *)
(* one compare-and-swap of the cell from EMPTY to FULL; past the segment's  *)
(* end it links a successor whose first cell already holds its value. A pop *)
(* reads both words to tell an empty queue, walks to the cell the head     *)
(* word names, claims it with a compare-and-swap of the head word and swaps *)
(* it to TAKEN: a FULL cell is its value, an EMPTY one is taken out of play *)
(* (its push retries). A try_pop answers Busy instead of taking an          *)
(* unwritten cell out of play. A pop that finds the head segment drained    *)
(* moves the head word and pointer on, the tail pointer first, and the      *)
(* winner of the head pointer's CAS retires the segment. kovan keeps a      *)
(* segment for an operation only when the operation reached it while it was *)
(* reachable (not yet retired): from an end, or by a walk step checked      *)
(* against the head pointer; it frees a retired segment once every          *)
(* operation that so holds it has ended.                                    *)
(*                                                                          *)
(* A segment is named by its id: the code allocates the successor of        *)
(* segment s with id s + 1, and only one successor of s is ever linked.     *)
(* The wait a pop makes on an unwritten cell (PATIENCE re-reads) is folded  *)
(* into its swap, which may come at any moment: every number of re-reads is *)
(* covered. A walk of pointers forward (locate, catch_up_tail) is one step, *)
(* as the pointers only move forward. A step that touches only the thread's *)
(* own state (a loop counter, a pin, an unpin) is folded into the shared    *)
(* step next to it, which no other thread can tell apart.                   *)
(*                                                                          *)
(* `Mutation` puts back one wrong rule at a time; see README.md.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Producers,  \* producer thread ids
    Consumers,  \* consumer thread ids
    K,          \* values each producer pushes, in order
    Pops,       \* operations each consumer makes
    Try,        \* TRUE: consumers call try_pop; FALSE: pop
    SEG,        \* cells per segment (32 in the code)
    MaxSegs,    \* segment ids 0 .. MaxSegs - 1 (the state constraint)
    Mutation    \* "none", or one wrong rule put back

NULL == -1
Segs == 0 .. (MaxSegs - 1)
Cells == 0 .. (SEG - 1)
\* The value producer p pushes k-th: p * 100 + k.
Val(p, k) == p * 100 + k
ProdOf(v) == v \div 100
SeqOf(v) == v % 100
Values == {Val(p, k) : p \in Producers, k \in 1 .. K}
Threads == Producers \cup Consumers
\* A queue position: the cell's place in the one order every thread agrees on.
Pos(s, i) == s * SEG + i
Min2(a, b) == IF a < b THEN a ELSE b
Max2(a, b) == IF a > b THEN a ELSE b

\* scan_pop: the earlier SegQueue's pop, which took the first FULL cell of the head segment and
\* passed over one still being written, so a consumer takes values out of queue order
\* (ConsumerOrder catches it).
MutScan == Mutation = "scan_pop"
\* no_poison: a pop that finds its claimed cell EMPTY moves on without taking it out of play, so
\* the late push writes its value where no pop will claim again (NoLoss catches it).
MutNoPoison == Mutation = "no_poison"
\* retire_before_tail: the head's walk retires a segment without first moving the tail pointer
\* off it, so a push can still reach it after it is freed (NoUseAfterFree catches it).
MutRetireEarly == Mutation = "retire_before_tail"
\* busy_without_view: try_pop answers Busy for an EMPTY cell without first telling, from the two
\* words, that a push claimed it (BusyMeansClaimed catches it).
MutBusyBlind == Mutation = "busy_without_view"
\* tail_before_head: a pop reads the tail word before the head word, so it can see the head past
\* values pushed after its tail read and answer None while they wait (EmptySound catches it).
MutTailFirst == Mutation = "tail_before_head"
\* link_then_retry: a push that linked the successor with its value in the first cell goes on
\* pushing the value, which then sits in two cells (UniqueTake catches it).
MutLinkRetry == Mutation = "link_then_retry"
\* store_tail_advance: advance_tail_word checks the word's segment, then stores the successor's
\* word instead of a compare-and-swap, which can move the word back over a cell whose claimer
\* has not written it (RealTimeOrder catches it).
MutStoreAdvance == Mutation = "store_tail_advance"
\* load_after_claim: a push loads the tail pointer after its claim, which can then name a
\* segment past the claimed one (NoUnlinkedClaim catches it).
MutLoadLate == Mutation = "load_after_claim"
\* retry_same_cell: a push whose cell was taken out of play retries its compare-and-swap on the
\* same cell instead of claiming another, forever (Termination catches it).
MutRetrySame == Mutation = "retry_same_cell"
\* walk_unchecked: the code before the fix: a walk steps onto every successor it loads, one a
\* segment the head had passed named included, which may be retired and is then kept for the
\* walker by nothing (NoUseAfterFree catches it).
MutWalkBlind == Mutation = "walk_unchecked"
\* claim_before_find: the code before the fix: a pop claims with a fetch-add on the head word and
\* walks to the cell after, so its claim can name a segment the head moves past, and retires,
\* before the walk gets there (NoLoss catches it: the walk finds the segment gone and the value in
\* the cell is never taken).
MutClaimFirst == Mutation = "claim_before_find"

\* What the two words say about the front of the queue (`classify`).
Classify(h, t) ==
    IF t.id = h.id
    THEN IF h.ix < Min2(t.ix, SEG) THEN "claimed"
         ELSE IF t.ix <= SEG THEN "empty" ELSE "drained"
    ELSE IF t.id + 1 = h.id
         THEN IF h.ix = 0 THEN "claimed" ELSE "empty"
         ELSE IF h.ix < SEG THEN "claimed" ELSE "drained"

(* --algorithm SegQueue
variables
    \* the cells: state and value
    cst = [s \in Segs |-> [i \in Cells |-> "EMPTY"]],
    cval = [s \in Segs |-> [i \in Cells |-> 0]],
    \* each segment's successor, and its life
    nxt = [s \in Segs |-> NULL],
    retired = {},
    freed = {},
    \* the operations that held each segment when it was retired: <<thread, operation number>>
    holders = [s \in Segs |-> {}],
    \* the segments each thread's operation reached while they were reachable
    prot = [t \in Threads |-> {}],
    \* the claim words and the segment pointers of the two ends
    tw = [id |-> 0, ix |-> 0],
    hw = [id |-> 0, ix |-> 0],
    tptr = 0,
    hptr = 0,
    \* each thread's operation number, and whether it is pinned in an operation
    opn = [t \in Threads |-> 0],
    busy = [t \in Threads |-> FALSE],
    \* histories: where each value was first written, the positions pushes and pops claimed, the
    \* values taken, the pushes that returned, the answers given, the broken checks
    pos = [x \in Values |-> NULL],
    claimsP = {},
    claimsC = {},
    took = {},
    done = {},
    said = {},
    errs = {},
    \* a procedure's answer to its caller
    rv = [t \in Threads |-> FALSE];

define
    \* A segment reached from pointer p on the way to id s is touched; a freed one is a use
    \* after free. Ids only grow along `nxt`, so the walk from p to s touches p .. s.
    Touch(p, s) == IF \E x \in p .. s : x \in freed THEN {"uaf"} ELSE {}
    \* Every segment from p to s is linked (the walk can reach s).
    Linked(p, s) == \A x \in p .. (s - 1) : nxt[x] = x + 1
    \* The segments a walk from p (loaded from an end) to s steps on: each successor is checked
    \* against the head pointer, and past it the walk goes on from the head pointer
    \* (walk_unchecked: every one from p to s).
    WalkSet(p, s) == IF MutWalkBlind THEN p .. s ELSE {p} \cup (Max2(p, hptr) .. s)
    \* The checked walk finds segment s gone: the head pointer moved past it.
    WalkGone(s) == ~MutWalkBlind /\ s < hptr
    \* A touch of a freed segment is a use after free.
    TouchSet(X) == IF X \cap freed # {} THEN {"uaf"} ELSE {}
    \* kovan keeps for the thread's operation the segments it reaches while they are reachable.
    Reached(t, X) == prot[t] \cup (X \ retired)
    AllDone == \A t \in Threads : pc[t] = "Done"
    \* RealTimeOrder: a push writes its value behind every push that returned before it began
    \* (`before`).
    RealTime(before, p) == IF \E a \in before : pos[a] > p THEN {"rt_order"} ELSE {}
    \* PopOrder: a pop takes a value behind every value taken before it began (`st`); UniqueTake:
    \* no value is taken twice.
    TakeCheck(st, p, v) ==
        (IF \E x \in st : pos[x] > p THEN {"pop_order"} ELSE {})
            \cup (IF v \in took THEN {"dup"} ELSE {})
    \* A value's position: where it was first written.
    FirstPos(v, p) == IF pos[v] = NULL THEN p ELSE pos[v]
    \* EmptySound: at the step that tells a pop the queue is empty, every push that has returned
    \* has its cell claimed by a pop.
    EmptyCheck == IF \E u \in done : pos[u] \notin claimsC THEN {"empty_unsound"} ELSE {}
end define;

\* catch_up_tail: the tail pointer walked forward to the tail word's segment (or as far as the
\* links go); a pop may have put it one past the word already.
macro CatchUpTail()
begin
    errs := errs \cup Touch(tptr, Min2(tw.id, MaxSegs - 1));
    tptr := IF tptr >= tw.id THEN tptr
            ELSE LET reach == {x \in tptr .. Min2(tw.id, MaxSegs - 1) : Linked(tptr, x)}
                 IN CHOOSE x \in reach : \A y \in reach : y <= x;
end macro;

\* advance_tail_word(s): move the tail word from full segment s to the successor's second cell.
macro AdvanceTailWord(s)
begin
    if tw.id = s then tw := [id |-> s + 1, ix |-> 1]; end if;
end macro;

\* A push returns: the unpin, and the producer's next value.
macro EndPush()
begin
    busy[self] := FALSE || k := k + 1 || lt := 0 || w := [id |-> 0, ix |-> 0] || nx := NULL
        || before := {};
end macro;

\* ---------------------------------------------------------------- the head's walk
\* catch_up_head: the head pointer walked to the head word's segment, retiring every segment it
\* moves past, the tail pointer moved off each one first.
procedure CatchUpHead()
variables lh = 0, hn = NULL;
begin
CH1: \* the head pointer
    lh := hptr;
CH2: \* the segment's id against the head word, then its link
    errs := errs \cup Touch(lh, lh);
    if lh = hw.id \/ nxt[lh] = NULL then
        return;
    else
        hn := nxt[lh];
    end if;
CH3: \* the tail pointer off the segment first
    if tptr = lh /\ ~MutRetireEarly then tptr := hn; end if;
CH4: \* the head pointer's CAS; its winner retires the segment, kept for the operations that
     \* hold it
    if hptr = lh then
        hptr := hn || retired := retired \cup {lh}
            || holders[lh] := {<<t, opn[t]>> : t \in {u \in Threads : busy[u] /\ lh \in prot[u]}};
    end if;
    goto CH1;
end procedure;

\* drained: the head segment `hs` has every cell claimed; move the head word on when a successor
\* exists. It answers TRUE in rv when the queue was empty.
procedure Drained(hs, lp)
begin
DR1: \* locate from the pointer `lp` the caller loaded, then the segment's link
    if hs < lp \/ WalkGone(hs) then
        rv[self] := FALSE;
        return;
    elsif nxt[hs] = NULL then
        errs := errs \cup TouchSet(WalkSet(lp, hs)) \cup EmptyCheck || rv[self] := TRUE
            || prot[self] := Reached(self, WalkSet(lp, hs));
        return;
    else
        errs := errs \cup TouchSet(WalkSet(lp, hs)) || prot[self] := Reached(self, WalkSet(lp, hs));
    end if;
DR2: \* the head word moved to the successor's first cell
    if hw.id = hs then hw := [id |-> hs + 1, ix |-> 0]; end if;
    rv[self] := FALSE;
    call CatchUpHead();
    return;
end procedure;

\* ---------------------------------------------------------------- pop
procedure Pop()
variables h0 = [id |-> 0, ix |-> 0], t0 = [id |-> 0, ix |-> 0], view = "", lh3 = 0,
    cw = [id |-> 0, ix |-> 0], startTaken = {}, snapped = FALSE, scan = 0;
begin
PO1: \* the two words, head then tail (no pin while the queue looks empty); the values taken
     \* when this pop began
    if MutTailFirst then t0 := tw; else h0 := hw; end if;
    startTaken := IF snapped THEN startTaken ELSE took || snapped := TRUE;
PO2:
    if Classify(IF MutTailFirst THEN hw ELSE h0, IF MutTailFirst THEN t0 ELSE tw) = "empty"
       /\ ~MutScan then
        said := said \cup {"none"} || busy[self] := FALSE || errs := errs \cup EmptyCheck;
        return;
    else
        view := Classify(IF MutTailFirst THEN hw ELSE h0, IF MutTailFirst THEN t0 ELSE tw)
            || h0 := IF MutTailFirst THEN hw ELSE h0;
    end if;
PO3: \* a pin, then the head pointer
    busy[self] := TRUE || opn[self] := IF busy[self] THEN opn[self] ELSE opn[self] + 1
        || lh3 := hptr || prot[self] := IF busy[self] THEN Reached(self, {hptr}) ELSE {hptr} \ retired;
    if MutScan then
        goto PS1;
    elsif MutClaimFirst /\ view = "drained" then
        call Drained(h0.id, lh3);
        goto PO6;
    elsif MutClaimFirst then
        goto PO4;
    end if;
PO3w: \* the words again, after the pointer: the head word
    h0 := hw;
PO3v: \* the tail word, and what the two say
    if Classify(h0, tw) = "empty" then
        said := said \cup {"none"} || busy[self] := FALSE || errs := errs \cup EmptyCheck;
        return;
    elsif Classify(h0, tw) = "drained" then
        call Drained(h0.id, lh3);
        goto PO6;
    elsif h0.id < lh3 \/ ~Linked(lh3, h0.id) \/ h0.ix >= SEG \/ WalkGone(h0.id) then
        goto PO3;
    end if;
PO7: \* locate the head word's cell
    errs := errs \cup TouchSet(WalkSet(lh3, h0.id)) || prot[self] := Reached(self, WalkSet(lh3, h0.id));
PO8: \* (the PATIENCE re-reads folded in) the claim, a compare-and-swap of the head word from h0,
     \* and the swap to TAKEN
    if hw # h0 then
        goto PO3;
    elsif cst[h0.id][h0.ix] = "FULL" then
        hw := [hw EXCEPT !.ix = @ + 1] || claimsC := claimsC \cup {Pos(h0.id, h0.ix)}
            || cst[h0.id][h0.ix] := "TAKEN" || took := took \cup {cval[h0.id][h0.ix]}
            || errs := errs \cup TouchSet({h0.id})
                \cup TakeCheck(startTaken, Pos(h0.id, h0.ix), cval[h0.id][h0.ix])
            || said := said \cup {"value"} || busy[self] := FALSE;
        return;
    elsif ~MutNoPoison then
        hw := [hw EXCEPT !.ix = @ + 1] || claimsC := claimsC \cup {Pos(h0.id, h0.ix)}
            || cst[h0.id][h0.ix] := "TAKEN" || errs := errs \cup TouchSet({h0.id});
        goto PO3;
    else
        hw := [hw EXCEPT !.ix = @ + 1] || claimsC := claimsC \cup {Pos(h0.id, h0.ix)};
        goto PO3;
    end if;
\* (claim_before_find) the earlier claim: head.word.fetch_add(1), then the walk to its cell
PO4:
    cw := hw || hw := [hw EXCEPT !.ix = @ + 1]
        || claimsC := IF hw.ix < SEG THEN claimsC \cup {Pos(hw.id, hw.ix)} ELSE claimsC;
    if cw.ix >= SEG then goto PO1; end if;
PO5: \* locate, and the swap to TAKEN (the PATIENCE re-reads folded into it); a segment the
     \* head passed is gone, with the cell
    if WalkGone(cw.id) then
        goto PO1;
    end if;
PO5w:
    errs := errs \cup TouchSet(WalkSet(lh3, cw.id))
        \cup (IF cw.id < lh3 \/ ~Linked(lh3, cw.id) THEN {"unlinked_claim"} ELSE {})
        \cup (IF cst[cw.id][cw.ix] = "FULL"
              THEN TakeCheck(startTaken, Pos(cw.id, cw.ix), cval[cw.id][cw.ix]) ELSE {})
        || prot[self] := Reached(self, WalkSet(lh3, cw.id));
    if cst[cw.id][cw.ix] = "FULL" then
        cst[cw.id][cw.ix] := "TAKEN" || took := took \cup {cval[cw.id][cw.ix]}
            || said := said \cup {"value"} || busy[self] := FALSE;
        return;
    elsif ~MutNoPoison then
        cst[cw.id][cw.ix] := "TAKEN";
        goto PO1;
    else
        goto PO1;
    end if;
PO6: \* after a drained view
    if rv[self] then
        said := said \cup {"none"} || busy[self] := FALSE || rv[self] := FALSE;
        return;
    else
        goto PO1;
    end if;
\* (scan_pop) the earlier pop: the first FULL cell of the head segment, passing over the rest
PS1:
    scan := 0;
PS2:
    if scan >= SEG then
        said := said \cup {"none"} || busy[self] := FALSE;
        return;
    elsif cst[lh3][scan] = "FULL" then
        cst[lh3][scan] := "TAKEN" || claimsC := claimsC \cup {Pos(lh3, scan)}
            || errs := errs \cup TakeCheck(startTaken, Pos(lh3, scan), cval[lh3][scan])
            || took := took \cup {cval[lh3][scan]}
            || said := said \cup {"value"} || busy[self] := FALSE;
        return;
    else
        scan := scan + 1;
        goto PS2;
    end if;
end procedure;

\* ---------------------------------------------------------------- try_pop
procedure TryPop()
variables lh4 = 0, h1 = [id |-> 0, ix |-> 0], startTaken = {};
begin
TP1: \* the two words (no pin while the queue looks empty); the values taken when it began
    h1 := hw || startTaken := took;
TP2:
    if Classify(h1, tw) = "empty" /\ ~MutBusyBlind then
        said := said \cup {"empty"} || errs := errs \cup EmptyCheck;
        return;
    end if;
TP3: \* a pin, the pointer first, then the words again
    busy[self] := TRUE || opn[self] := IF busy[self] THEN opn[self] ELSE opn[self] + 1
        || lh4 := hptr || prot[self] := IF busy[self] THEN Reached(self, {hptr}) ELSE {hptr} \ retired;
TP4:
    h1 := hw;
TP5:
    if ~MutBusyBlind /\ Classify(h1, tw) = "empty" then
        said := said \cup {"empty"} || busy[self] := FALSE || errs := errs \cup EmptyCheck;
        return;
    elsif ~MutBusyBlind /\ Classify(h1, tw) = "drained" then
        call Drained(h1.id, lh4);
        goto TP7;
    elsif h1.id < lh4 \/ ~Linked(lh4, h1.id) \/ h1.ix >= SEG \/ WalkGone(h1.id) then
        goto TP3;
    end if;
TP6: \* locate the head word's cell and read its state; claim a FULL one by the CAS of the head
     \* word from h1 to h1 + 1 (a cell read FULL stays FULL until its claimer takes it, and that
     \* claim moves the word, so the read and the CAS fold into one step)
    if cst[h1.id][h1.ix] = "EMPTY" then
        \* BusyMeansClaimed: a push claimed this cell and has not written it
        errs := errs \cup TouchSet(WalkSet(lh4, h1.id))
            \cup (IF Pos(h1.id, h1.ix) \notin claimsP THEN {"busy_unclaimed"} ELSE {})
            || said := said \cup {"busy"} || busy[self] := FALSE;
        return;
    elsif cst[h1.id][h1.ix] = "FULL" /\ hw = h1 then
        errs := errs \cup TouchSet(WalkSet(lh4, h1.id))
            || hw := [hw EXCEPT !.ix = @ + 1] || claimsC := claimsC \cup {Pos(h1.id, h1.ix)}
            || prot[self] := Reached(self, WalkSet(lh4, h1.id));
        goto TP8;
    else
        errs := errs \cup TouchSet(WalkSet(lh4, h1.id)) || prot[self] := Reached(self, WalkSet(lh4, h1.id));
        goto TP3;
    end if;
TP7:
    if rv[self] then
        said := said \cup {"empty"} || busy[self] := FALSE || rv[self] := FALSE;
        return;
    else
        goto TP3;
    end if;
TP8: \* the swap to TAKEN of the claimed cell
    if cst[h1.id][h1.ix] = "FULL" then
        cst[h1.id][h1.ix] := "TAKEN" || took := took \cup {cval[h1.id][h1.ix]}
            || errs := errs \cup TouchSet({h1.id})
                \cup TakeCheck(startTaken, Pos(h1.id, h1.ix), cval[h1.id][h1.ix])
            || said := said \cup {"value"} || busy[self] := FALSE;
        return;
    else
        errs := errs \cup TouchSet({h1.id});
        goto TP3;
    end if;
end procedure;

\* ---------------------------------------------------------------- push, inlined in its thread
process Producer \in Producers
variables k = 1, lt = 0, w = [id |-> 0, ix |-> 0], nx = NULL, before = {};
begin
PU1: \* a push begins: the pin, the pushes that had returned, then tail.seg.load
    if k <= K then
        opn[self] := opn[self] + 1 || busy[self] := TRUE || before := done
            || lt := IF MutLoadLate THEN lt ELSE tptr
            || prot[self] := IF MutLoadLate THEN {} ELSE {tptr} \ retired;
        goto PU3;
    else
        goto Done;
    end if;
PU2: \* a retry: tail.seg.load
    if ~MutLoadLate then lt := tptr || prot[self] := Reached(self, {tptr}); end if;
PU3: \* tail.word.fetch_add(1)
    w := tw || tw := [tw EXCEPT !.ix = @ + 1]
        || claimsP := IF tw.ix < SEG THEN claimsP \cup {Pos(tw.id, tw.ix)} ELSE claimsP;
    if MutLoadLate then goto PU3m; elsif w.ix >= SEG then goto PU5; else goto PU4; end if;
PU3m: \* (load_after_claim) tail.seg.load after the claim
    lt := tptr || prot[self] := Reached(self, {tptr});
    if w.ix >= SEG then goto PU5; end if;
PU4: \* locate; the head pointer past the claim's segment: a pop took the cell out of play
    if WalkGone(w.id) then
        goto PU2;
    end if;
PU4w:
    errs := errs \cup TouchSet(WalkSet(lt, w.id))
        \* the claim names a segment at or past the pointer loaded before it, linked
        \cup (IF w.id < lt \/ ~Linked(lt, w.id) THEN {"unlinked_claim"} ELSE {})
        || prot[self] := Reached(self, WalkSet(lt, w.id));
    if w.id < lt \/ ~Linked(lt, w.id) then
        goto PU2;
    elsif w.id = lt then
        goto PU4b;
    end if;
PU4a: \* the pointer lags behind the word: catch_up_tail
    CatchUpTail();
PU4b: \* the value written, the cell's compare-and-swap EMPTY -> FULL
    if cst[w.id][w.ix] = "EMPTY" then
        cst[w.id][w.ix] := "FULL" || cval[w.id][w.ix] := Val(self, k)
            || pos[Val(self, k)] := FirstPos(Val(self, k), Pos(w.id, w.ix))
            || done := done \cup {Val(self, k)}
            || errs := errs \cup TouchSet({w.id}) \cup RealTime(before, Pos(w.id, w.ix));
        EndPush();
        goto PU1;
    elsif MutRetrySame then
        errs := errs \cup TouchSet({w.id});
        goto PU4b;
    else
        \* a pop took the cell out of play: the value is still this push's
        errs := errs \cup TouchSet({w.id});
        goto PU2;
    end if;
PU5: \* segment `w.id` is full: follow the pointer a pop moved past it, or locate it
    if w.id < lt \/ WalkGone(w.id) then
        AdvanceTailWord(w.id);
        goto PU2;
    else
        errs := errs \cup TouchSet(WalkSet(lt, w.id)) || nx := nxt[w.id]
            || prot[self] := Reached(self, WalkSet(lt, w.id));
    end if;
PU6: \* link the successor whose first cell holds this push's value, or meet the one linked
    if nx = NULL /\ nxt[w.id] = NULL /\ w.id + 1 >= MaxSegs then
        errs := errs \cup {"bound"};
        EndPush();
        goto PU1;
    elsif nx = NULL /\ nxt[w.id] = NULL then
        nxt[w.id] := w.id + 1 || cst[w.id + 1][0] := "FULL" || cval[w.id + 1][0] := Val(self, k)
            || pos[Val(self, k)] := FirstPos(Val(self, k), Pos(w.id + 1, 0))
            || claimsP := claimsP \cup {Pos(w.id + 1, 0)}
            || errs := errs \cup TouchSet({w.id}) \cup RealTime(before, Pos(w.id + 1, 0))
            || nx := w.id + 1;
    elsif nx = NULL then
        \* the compare-and-swap of `next` failed: another push linked the successor
        errs := errs \cup TouchSet({w.id}) || nx := nxt[w.id];
    end if;
PU7: \* advance_tail: the word first
    if MutStoreAdvance /\ tw.id = w.id then
        goto PU7s;
    else
        AdvanceTailWord(w.id);
        goto PU8;
    end if;
PU7s: \* (store_tail_advance) the word stored after its segment was checked
    tw := [id |-> w.id + 1, ix |-> 1];
PU8: \* then the pointer; a push that linked the successor returns
    if lt = w.id then
        if tptr = lt then tptr := nx; end if;
    else
        CatchUpTail();
    end if;
    if pos[Val(self, k)] # NULL /\ ~MutLinkRetry then
        \* the push that linked returns only now: its value was in the queue from the link on
        done := done \cup {Val(self, k)};
        EndPush();
        goto PU1;
    else
        goto PU2;
    end if;
end process;

process Consumer \in Consumers
variables n = 0;
begin
CO1:
    while n < Pops do
        n := n + 1;
        if Try then call TryPop(); else call Pop(); end if;
    end while;
end process;

\* kovan's reclamation: a retired segment is freed once every operation that held it when it was
\* retired (reached it while it was reachable) has ended (`retire_reclaimable`, guard drop).
process Reclaimer = 0
begin
RC1:
    while ~AllDone do
        with s \in {x \in retired \ freed :
                    \A h \in holders[x] : opn[h[1]] # h[2] \/ ~busy[h[1]]} do
            freed := freed \cup {s};
        end with;
    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "bf84f72b" /\ chksum(tla) = "80f0bda3")
\* Procedure variable startTaken of procedure Pop at line 247 col 32 changed to startTaken_
CONSTANT defaultInitValue
VARIABLES cst, cval, nxt, retired, freed, holders, prot, tw, hw, tptr, hptr, 
          opn, busy, pos, claimsP, claimsC, took, done, said, errs, rv, pc, 
          stack

(* define statement *)
Touch(p, s) == IF \E x \in p .. s : x \in freed THEN {"uaf"} ELSE {}

Linked(p, s) == \A x \in p .. (s - 1) : nxt[x] = x + 1



WalkSet(p, s) == IF MutWalkBlind THEN p .. s ELSE {p} \cup (Max2(p, hptr) .. s)

WalkGone(s) == ~MutWalkBlind /\ s < hptr

TouchSet(X) == IF X \cap freed # {} THEN {"uaf"} ELSE {}

Reached(t, X) == prot[t] \cup (X \ retired)
AllDone == \A t \in Threads : pc[t] = "Done"


RealTime(before, p) == IF \E a \in before : pos[a] > p THEN {"rt_order"} ELSE {}


TakeCheck(st, p, v) ==
    (IF \E x \in st : pos[x] > p THEN {"pop_order"} ELSE {})
        \cup (IF v \in took THEN {"dup"} ELSE {})

FirstPos(v, p) == IF pos[v] = NULL THEN p ELSE pos[v]


EmptyCheck == IF \E u \in done : pos[u] \notin claimsC THEN {"empty_unsound"} ELSE {}

VARIABLES lh, hn, hs, lp, h0, t0, view, lh3, cw, startTaken_, snapped, scan, 
          lh4, h1, startTaken, k, lt, w, nx, before, n

vars == << cst, cval, nxt, retired, freed, holders, prot, tw, hw, tptr, hptr, 
           opn, busy, pos, claimsP, claimsC, took, done, said, errs, rv, pc, 
           stack, lh, hn, hs, lp, h0, t0, view, lh3, cw, startTaken_, snapped, 
           scan, lh4, h1, startTaken, k, lt, w, nx, before, n >>

ProcSet == (Producers) \cup (Consumers) \cup {0}

Init == (* Global variables *)
        /\ cst = [s \in Segs |-> [i \in Cells |-> "EMPTY"]]
        /\ cval = [s \in Segs |-> [i \in Cells |-> 0]]
        /\ nxt = [s \in Segs |-> NULL]
        /\ retired = {}
        /\ freed = {}
        /\ holders = [s \in Segs |-> {}]
        /\ prot = [t \in Threads |-> {}]
        /\ tw = [id |-> 0, ix |-> 0]
        /\ hw = [id |-> 0, ix |-> 0]
        /\ tptr = 0
        /\ hptr = 0
        /\ opn = [t \in Threads |-> 0]
        /\ busy = [t \in Threads |-> FALSE]
        /\ pos = [x \in Values |-> NULL]
        /\ claimsP = {}
        /\ claimsC = {}
        /\ took = {}
        /\ done = {}
        /\ said = {}
        /\ errs = {}
        /\ rv = [t \in Threads |-> FALSE]
        (* Procedure CatchUpHead *)
        /\ lh = [ self \in ProcSet |-> 0]
        /\ hn = [ self \in ProcSet |-> NULL]
        (* Procedure Drained *)
        /\ hs = [ self \in ProcSet |-> defaultInitValue]
        /\ lp = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Pop *)
        /\ h0 = [ self \in ProcSet |-> [id |-> 0, ix |-> 0]]
        /\ t0 = [ self \in ProcSet |-> [id |-> 0, ix |-> 0]]
        /\ view = [ self \in ProcSet |-> ""]
        /\ lh3 = [ self \in ProcSet |-> 0]
        /\ cw = [ self \in ProcSet |-> [id |-> 0, ix |-> 0]]
        /\ startTaken_ = [ self \in ProcSet |-> {}]
        /\ snapped = [ self \in ProcSet |-> FALSE]
        /\ scan = [ self \in ProcSet |-> 0]
        (* Procedure TryPop *)
        /\ lh4 = [ self \in ProcSet |-> 0]
        /\ h1 = [ self \in ProcSet |-> [id |-> 0, ix |-> 0]]
        /\ startTaken = [ self \in ProcSet |-> {}]
        (* Process Producer *)
        /\ k = [self \in Producers |-> 1]
        /\ lt = [self \in Producers |-> 0]
        /\ w = [self \in Producers |-> [id |-> 0, ix |-> 0]]
        /\ nx = [self \in Producers |-> NULL]
        /\ before = [self \in Producers |-> {}]
        (* Process Consumer *)
        /\ n = [self \in Consumers |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> CASE self \in Producers -> "PU1"
                                        [] self \in Consumers -> "CO1"
                                        [] self = 0 -> "RC1"]

CH1(self) == /\ pc[self] = "CH1"
             /\ lh' = [lh EXCEPT ![self] = hptr]
             /\ pc' = [pc EXCEPT ![self] = "CH2"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, rv, stack, hn, hs, lp, h0, 
                             t0, view, lh3, cw, startTaken_, snapped, scan, 
                             lh4, h1, startTaken, k, lt, w, nx, before, n >>

CH2(self) == /\ pc[self] = "CH2"
             /\ errs' = (errs \cup Touch(lh[self], lh[self]))
             /\ IF lh[self] = hw.id \/ nxt[lh[self]] = NULL
                   THEN /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lh' = [lh EXCEPT ![self] = Head(stack[self]).lh]
                        /\ hn' = [hn EXCEPT ![self] = Head(stack[self]).hn]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ hn' = [hn EXCEPT ![self] = nxt[lh[self]]]
                        /\ pc' = [pc EXCEPT ![self] = "CH3"]
                        /\ UNCHANGED << stack, lh >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, rv, hs, lp, h0, t0, view, lh3, 
                             cw, startTaken_, snapped, scan, lh4, h1, 
                             startTaken, k, lt, w, nx, before, n >>

CH3(self) == /\ pc[self] = "CH3"
             /\ IF tptr = lh[self] /\ ~MutRetireEarly
                   THEN /\ tptr' = hn[self]
                   ELSE /\ TRUE
                        /\ tptr' = tptr
             /\ pc' = [pc EXCEPT ![self] = "CH4"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, hptr, opn, busy, pos, claimsP, claimsC, took, 
                             done, said, errs, rv, stack, lh, hn, hs, lp, h0, 
                             t0, view, lh3, cw, startTaken_, snapped, scan, 
                             lh4, h1, startTaken, k, lt, w, nx, before, n >>

CH4(self) == /\ pc[self] = "CH4"
             /\ IF hptr = lh[self]
                   THEN /\ /\ holders' = [holders EXCEPT ![lh[self]] = {<<t, opn[t]>> : t \in {u \in Threads : busy[u] /\ lh[self] \in prot[u]}}]
                           /\ hptr' = hn[self]
                           /\ retired' = (retired \cup {lh[self]})
                   ELSE /\ TRUE
                        /\ UNCHANGED << retired, holders, hptr >>
             /\ pc' = [pc EXCEPT ![self] = "CH1"]
             /\ UNCHANGED << cst, cval, nxt, freed, prot, tw, hw, tptr, opn, 
                             busy, pos, claimsP, claimsC, took, done, said, 
                             errs, rv, stack, lh, hn, hs, lp, h0, t0, view, 
                             lh3, cw, startTaken_, snapped, scan, lh4, h1, 
                             startTaken, k, lt, w, nx, before, n >>

CatchUpHead(self) == CH1(self) \/ CH2(self) \/ CH3(self) \/ CH4(self)

DR1(self) == /\ pc[self] = "DR1"
             /\ IF hs[self] < lp[self] \/ WalkGone(hs[self])
                   THEN /\ rv' = [rv EXCEPT ![self] = FALSE]
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ hs' = [hs EXCEPT ![self] = Head(stack[self]).hs]
                        /\ lp' = [lp EXCEPT ![self] = Head(stack[self]).lp]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << prot, errs >>
                   ELSE /\ IF nxt[hs[self]] = NULL
                              THEN /\ /\ errs' = (errs \cup TouchSet(WalkSet(lp[self], hs[self])) \cup EmptyCheck)
                                      /\ prot' = [prot EXCEPT ![self] = Reached(self, WalkSet(lp[self], hs[self]))]
                                      /\ rv' = [rv EXCEPT ![self] = TRUE]
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ hs' = [hs EXCEPT ![self] = Head(stack[self]).hs]
                                   /\ lp' = [lp EXCEPT ![self] = Head(stack[self]).lp]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              ELSE /\ /\ errs' = (errs \cup TouchSet(WalkSet(lp[self], hs[self])))
                                      /\ prot' = [prot EXCEPT ![self] = Reached(self, WalkSet(lp[self], hs[self]))]
                                   /\ pc' = [pc EXCEPT ![self] = "DR2"]
                                   /\ UNCHANGED << rv, stack, hs, lp >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, tw, hw, 
                             tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, lh, hn, h0, t0, view, lh3, cw, 
                             startTaken_, snapped, scan, lh4, h1, startTaken, 
                             k, lt, w, nx, before, n >>

DR2(self) == /\ pc[self] = "DR2"
             /\ IF hw.id = hs[self]
                   THEN /\ hw' = [id |-> hs[self] + 1, ix |-> 0]
                   ELSE /\ TRUE
                        /\ hw' = hw
             /\ rv' = [rv EXCEPT ![self] = FALSE]
             /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "CatchUpHead",
                                                      pc        |->  Head(stack[self]).pc,
                                                      lh        |->  lh[self],
                                                      hn        |->  hn[self] ] >>
                                                  \o Tail(stack[self])]
             /\ lh' = [lh EXCEPT ![self] = 0]
             /\ hn' = [hn EXCEPT ![self] = NULL]
             /\ pc' = [pc EXCEPT ![self] = "CH1"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, hs, lp, h0, t0, view, lh3, 
                             cw, startTaken_, snapped, scan, lh4, h1, 
                             startTaken, k, lt, w, nx, before, n >>

Drained(self) == DR1(self) \/ DR2(self)

PO1(self) == /\ pc[self] = "PO1"
             /\ IF MutTailFirst
                   THEN /\ t0' = [t0 EXCEPT ![self] = tw]
                        /\ h0' = h0
                   ELSE /\ h0' = [h0 EXCEPT ![self] = hw]
                        /\ t0' = t0
             /\ /\ snapped' = [snapped EXCEPT ![self] = TRUE]
                /\ startTaken_' = [startTaken_ EXCEPT ![self] = IF snapped[self] THEN startTaken_[self] ELSE took]
             /\ pc' = [pc EXCEPT ![self] = "PO2"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, rv, stack, lh, hn, hs, lp, 
                             view, lh3, cw, scan, lh4, h1, startTaken, k, lt, 
                             w, nx, before, n >>

PO2(self) == /\ pc[self] = "PO2"
             /\ IF Classify(IF MutTailFirst THEN hw ELSE h0[self], IF MutTailFirst THEN t0[self] ELSE tw) = "empty"
                   /\ ~MutScan
                   THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                           /\ errs' = (errs \cup EmptyCheck)
                           /\ said' = (said \cup {"none"})
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ h0' = [h0 EXCEPT ![self] = Head(stack[self]).h0]
                        /\ t0' = [t0 EXCEPT ![self] = Head(stack[self]).t0]
                        /\ view' = [view EXCEPT ![self] = Head(stack[self]).view]
                        /\ lh3' = [lh3 EXCEPT ![self] = Head(stack[self]).lh3]
                        /\ cw' = [cw EXCEPT ![self] = Head(stack[self]).cw]
                        /\ startTaken_' = [startTaken_ EXCEPT ![self] = Head(stack[self]).startTaken_]
                        /\ snapped' = [snapped EXCEPT ![self] = Head(stack[self]).snapped]
                        /\ scan' = [scan EXCEPT ![self] = Head(stack[self]).scan]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ /\ h0' = [h0 EXCEPT ![self] = IF MutTailFirst THEN hw ELSE h0[self]]
                           /\ view' = [view EXCEPT ![self] = Classify(IF MutTailFirst THEN hw ELSE h0[self], IF MutTailFirst THEN t0[self] ELSE tw)]
                        /\ pc' = [pc EXCEPT ![self] = "PO3"]
                        /\ UNCHANGED << busy, said, errs, stack, t0, lh3, cw, 
                                        startTaken_, snapped, scan >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, pos, claimsP, claimsC, took, 
                             done, rv, lh, hn, hs, lp, lh4, h1, startTaken, k, 
                             lt, w, nx, before, n >>

PO3(self) == /\ pc[self] = "PO3"
             /\ /\ busy' = [busy EXCEPT ![self] = TRUE]
                /\ lh3' = [lh3 EXCEPT ![self] = hptr]
                /\ opn' = [opn EXCEPT ![self] = IF busy[self] THEN opn[self] ELSE opn[self] + 1]
                /\ prot' = [prot EXCEPT ![self] = IF busy[self] THEN Reached(self, {hptr}) ELSE {hptr} \ retired]
             /\ IF MutScan
                   THEN /\ pc' = [pc EXCEPT ![self] = "PS1"]
                        /\ UNCHANGED << stack, hs, lp >>
                   ELSE /\ IF MutClaimFirst /\ view[self] = "drained"
                              THEN /\ /\ hs' = [hs EXCEPT ![self] = h0[self].id]
                                      /\ lp' = [lp EXCEPT ![self] = lh3'[self]]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Drained",
                                                                               pc        |->  "PO6",
                                                                               hs        |->  hs[self],
                                                                               lp        |->  lp[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "DR1"]
                              ELSE /\ IF MutClaimFirst
                                         THEN /\ pc' = [pc EXCEPT ![self] = "PO4"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "PO3w"]
                                   /\ UNCHANGED << stack, hs, lp >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, tw, hw, 
                             tptr, hptr, pos, claimsP, claimsC, took, done, 
                             said, errs, rv, lh, hn, h0, t0, view, cw, 
                             startTaken_, snapped, scan, lh4, h1, startTaken, 
                             k, lt, w, nx, before, n >>

PO3w(self) == /\ pc[self] = "PO3w"
              /\ h0' = [h0 EXCEPT ![self] = hw]
              /\ pc' = [pc EXCEPT ![self] = "PO3v"]
              /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, 
                              tw, hw, tptr, hptr, opn, busy, pos, claimsP, 
                              claimsC, took, done, said, errs, rv, stack, lh, 
                              hn, hs, lp, t0, view, lh3, cw, startTaken_, 
                              snapped, scan, lh4, h1, startTaken, k, lt, w, nx, 
                              before, n >>

PO3v(self) == /\ pc[self] = "PO3v"
              /\ IF Classify(h0[self], tw) = "empty"
                    THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                            /\ errs' = (errs \cup EmptyCheck)
                            /\ said' = (said \cup {"none"})
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ h0' = [h0 EXCEPT ![self] = Head(stack[self]).h0]
                         /\ t0' = [t0 EXCEPT ![self] = Head(stack[self]).t0]
                         /\ view' = [view EXCEPT ![self] = Head(stack[self]).view]
                         /\ lh3' = [lh3 EXCEPT ![self] = Head(stack[self]).lh3]
                         /\ cw' = [cw EXCEPT ![self] = Head(stack[self]).cw]
                         /\ startTaken_' = [startTaken_ EXCEPT ![self] = Head(stack[self]).startTaken_]
                         /\ snapped' = [snapped EXCEPT ![self] = Head(stack[self]).snapped]
                         /\ scan' = [scan EXCEPT ![self] = Head(stack[self]).scan]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                         /\ UNCHANGED << hs, lp >>
                    ELSE /\ IF Classify(h0[self], tw) = "drained"
                               THEN /\ /\ hs' = [hs EXCEPT ![self] = h0[self].id]
                                       /\ lp' = [lp EXCEPT ![self] = lh3[self]]
                                       /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Drained",
                                                                                pc        |->  "PO6",
                                                                                hs        |->  hs[self],
                                                                                lp        |->  lp[self] ] >>
                                                                            \o stack[self]]
                                    /\ pc' = [pc EXCEPT ![self] = "DR1"]
                               ELSE /\ IF h0[self].id < lh3[self] \/ ~Linked(lh3[self], h0[self].id) \/ h0[self].ix >= SEG \/ WalkGone(h0[self].id)
                                          THEN /\ pc' = [pc EXCEPT ![self] = "PO3"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "PO7"]
                                    /\ UNCHANGED << stack, hs, lp >>
                         /\ UNCHANGED << busy, said, errs, h0, t0, view, lh3, 
                                         cw, startTaken_, snapped, scan >>
              /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, 
                              tw, hw, tptr, hptr, opn, pos, claimsP, claimsC, 
                              took, done, rv, lh, hn, lh4, h1, startTaken, k, 
                              lt, w, nx, before, n >>

PO7(self) == /\ pc[self] = "PO7"
             /\ /\ errs' = (errs \cup TouchSet(WalkSet(lh3[self], h0[self].id)))
                /\ prot' = [prot EXCEPT ![self] = Reached(self, WalkSet(lh3[self], h0[self].id))]
             /\ pc' = [pc EXCEPT ![self] = "PO8"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, tw, hw, 
                             tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, rv, stack, lh, hn, hs, lp, h0, 
                             t0, view, lh3, cw, startTaken_, snapped, scan, 
                             lh4, h1, startTaken, k, lt, w, nx, before, n >>

PO8(self) == /\ pc[self] = "PO8"
             /\ IF hw # h0[self]
                   THEN /\ pc' = [pc EXCEPT ![self] = "PO3"]
                        /\ UNCHANGED << cst, hw, busy, claimsC, took, said, 
                                        errs, stack, h0, t0, view, lh3, cw, 
                                        startTaken_, snapped, scan >>
                   ELSE /\ IF cst[h0[self].id][h0[self].ix] = "FULL"
                              THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                                      /\ claimsC' = (claimsC \cup {Pos(h0[self].id, h0[self].ix)})
                                      /\ cst' = [cst EXCEPT ![h0[self].id][h0[self].ix] = "TAKEN"]
                                      /\ errs' = (       errs \cup TouchSet({h0[self].id})
                                                  \cup TakeCheck(startTaken_[self], Pos(h0[self].id, h0[self].ix), cval[h0[self].id][h0[self].ix]))
                                      /\ hw' = [hw EXCEPT !.ix = @ + 1]
                                      /\ said' = (said \cup {"value"})
                                      /\ took' = (took \cup {cval[h0[self].id][h0[self].ix]})
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ h0' = [h0 EXCEPT ![self] = Head(stack[self]).h0]
                                   /\ t0' = [t0 EXCEPT ![self] = Head(stack[self]).t0]
                                   /\ view' = [view EXCEPT ![self] = Head(stack[self]).view]
                                   /\ lh3' = [lh3 EXCEPT ![self] = Head(stack[self]).lh3]
                                   /\ cw' = [cw EXCEPT ![self] = Head(stack[self]).cw]
                                   /\ startTaken_' = [startTaken_ EXCEPT ![self] = Head(stack[self]).startTaken_]
                                   /\ snapped' = [snapped EXCEPT ![self] = Head(stack[self]).snapped]
                                   /\ scan' = [scan EXCEPT ![self] = Head(stack[self]).scan]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              ELSE /\ IF ~MutNoPoison
                                         THEN /\ /\ claimsC' = (claimsC \cup {Pos(h0[self].id, h0[self].ix)})
                                                 /\ cst' = [cst EXCEPT ![h0[self].id][h0[self].ix] = "TAKEN"]
                                                 /\ errs' = (errs \cup TouchSet({h0[self].id}))
                                                 /\ hw' = [hw EXCEPT !.ix = @ + 1]
                                              /\ pc' = [pc EXCEPT ![self] = "PO3"]
                                         ELSE /\ /\ claimsC' = (claimsC \cup {Pos(h0[self].id, h0[self].ix)})
                                                 /\ hw' = [hw EXCEPT !.ix = @ + 1]
                                              /\ pc' = [pc EXCEPT ![self] = "PO3"]
                                              /\ UNCHANGED << cst, errs >>
                                   /\ UNCHANGED << busy, took, said, stack, h0, 
                                                   t0, view, lh3, cw, 
                                                   startTaken_, snapped, scan >>
             /\ UNCHANGED << cval, nxt, retired, freed, holders, prot, tw, 
                             tptr, hptr, opn, pos, claimsP, done, rv, lh, hn, 
                             hs, lp, lh4, h1, startTaken, k, lt, w, nx, before, 
                             n >>

PO4(self) == /\ pc[self] = "PO4"
             /\ /\ claimsC' = (IF hw.ix < SEG THEN claimsC \cup {Pos(hw.id, hw.ix)} ELSE claimsC)
                /\ cw' = [cw EXCEPT ![self] = hw]
                /\ hw' = [hw EXCEPT !.ix = @ + 1]
             /\ IF cw'[self].ix >= SEG
                   THEN /\ pc' = [pc EXCEPT ![self] = "PO1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PO5"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             tptr, hptr, opn, busy, pos, claimsP, took, done, 
                             said, errs, rv, stack, lh, hn, hs, lp, h0, t0, 
                             view, lh3, startTaken_, snapped, scan, lh4, h1, 
                             startTaken, k, lt, w, nx, before, n >>

PO5(self) == /\ pc[self] = "PO5"
             /\ IF WalkGone(cw[self].id)
                   THEN /\ pc' = [pc EXCEPT ![self] = "PO1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PO5w"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, rv, stack, lh, hn, hs, lp, 
                             h0, t0, view, lh3, cw, startTaken_, snapped, scan, 
                             lh4, h1, startTaken, k, lt, w, nx, before, n >>

PO5w(self) == /\ pc[self] = "PO5w"
              /\ /\ errs' = (    errs \cup TouchSet(WalkSet(lh3[self], cw[self].id))
                             \cup (IF cw[self].id < lh3[self] \/ ~Linked(lh3[self], cw[self].id) THEN {"unlinked_claim"} ELSE {})
                             \cup (IF cst[cw[self].id][cw[self].ix] = "FULL"
                                   THEN TakeCheck(startTaken_[self], Pos(cw[self].id, cw[self].ix), cval[cw[self].id][cw[self].ix]) ELSE {}))
                 /\ prot' = [prot EXCEPT ![self] = Reached(self, WalkSet(lh3[self], cw[self].id))]
              /\ IF cst[cw[self].id][cw[self].ix] = "FULL"
                    THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                            /\ cst' = [cst EXCEPT ![cw[self].id][cw[self].ix] = "TAKEN"]
                            /\ said' = (said \cup {"value"})
                            /\ took' = (took \cup {cval[cw[self].id][cw[self].ix]})
                         /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                         /\ h0' = [h0 EXCEPT ![self] = Head(stack[self]).h0]
                         /\ t0' = [t0 EXCEPT ![self] = Head(stack[self]).t0]
                         /\ view' = [view EXCEPT ![self] = Head(stack[self]).view]
                         /\ lh3' = [lh3 EXCEPT ![self] = Head(stack[self]).lh3]
                         /\ cw' = [cw EXCEPT ![self] = Head(stack[self]).cw]
                         /\ startTaken_' = [startTaken_ EXCEPT ![self] = Head(stack[self]).startTaken_]
                         /\ snapped' = [snapped EXCEPT ![self] = Head(stack[self]).snapped]
                         /\ scan' = [scan EXCEPT ![self] = Head(stack[self]).scan]
                         /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                    ELSE /\ IF ~MutNoPoison
                               THEN /\ cst' = [cst EXCEPT ![cw[self].id][cw[self].ix] = "TAKEN"]
                                    /\ pc' = [pc EXCEPT ![self] = "PO1"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "PO1"]
                                    /\ cst' = cst
                         /\ UNCHANGED << busy, took, said, stack, h0, t0, view, 
                                         lh3, cw, startTaken_, snapped, scan >>
              /\ UNCHANGED << cval, nxt, retired, freed, holders, tw, hw, tptr, 
                              hptr, opn, pos, claimsP, claimsC, done, rv, lh, 
                              hn, hs, lp, lh4, h1, startTaken, k, lt, w, nx, 
                              before, n >>

PO6(self) == /\ pc[self] = "PO6"
             /\ IF rv[self]
                   THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                           /\ rv' = [rv EXCEPT ![self] = FALSE]
                           /\ said' = (said \cup {"none"})
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ h0' = [h0 EXCEPT ![self] = Head(stack[self]).h0]
                        /\ t0' = [t0 EXCEPT ![self] = Head(stack[self]).t0]
                        /\ view' = [view EXCEPT ![self] = Head(stack[self]).view]
                        /\ lh3' = [lh3 EXCEPT ![self] = Head(stack[self]).lh3]
                        /\ cw' = [cw EXCEPT ![self] = Head(stack[self]).cw]
                        /\ startTaken_' = [startTaken_ EXCEPT ![self] = Head(stack[self]).startTaken_]
                        /\ snapped' = [snapped EXCEPT ![self] = Head(stack[self]).snapped]
                        /\ scan' = [scan EXCEPT ![self] = Head(stack[self]).scan]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PO1"]
                        /\ UNCHANGED << busy, said, rv, stack, h0, t0, view, 
                                        lh3, cw, startTaken_, snapped, scan >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, pos, claimsP, claimsC, took, 
                             done, errs, lh, hn, hs, lp, lh4, h1, startTaken, 
                             k, lt, w, nx, before, n >>

PS1(self) == /\ pc[self] = "PS1"
             /\ scan' = [scan EXCEPT ![self] = 0]
             /\ pc' = [pc EXCEPT ![self] = "PS2"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, rv, stack, lh, hn, hs, lp, 
                             h0, t0, view, lh3, cw, startTaken_, snapped, lh4, 
                             h1, startTaken, k, lt, w, nx, before, n >>

PS2(self) == /\ pc[self] = "PS2"
             /\ IF scan[self] >= SEG
                   THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                           /\ said' = (said \cup {"none"})
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ h0' = [h0 EXCEPT ![self] = Head(stack[self]).h0]
                        /\ t0' = [t0 EXCEPT ![self] = Head(stack[self]).t0]
                        /\ view' = [view EXCEPT ![self] = Head(stack[self]).view]
                        /\ lh3' = [lh3 EXCEPT ![self] = Head(stack[self]).lh3]
                        /\ cw' = [cw EXCEPT ![self] = Head(stack[self]).cw]
                        /\ startTaken_' = [startTaken_ EXCEPT ![self] = Head(stack[self]).startTaken_]
                        /\ snapped' = [snapped EXCEPT ![self] = Head(stack[self]).snapped]
                        /\ scan' = [scan EXCEPT ![self] = Head(stack[self]).scan]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << cst, claimsC, took, errs >>
                   ELSE /\ IF cst[lh3[self]][scan[self]] = "FULL"
                              THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                                      /\ claimsC' = (claimsC \cup {Pos(lh3[self], scan[self])})
                                      /\ cst' = [cst EXCEPT ![lh3[self]][scan[self]] = "TAKEN"]
                                      /\ errs' = (errs \cup TakeCheck(startTaken_[self], Pos(lh3[self], scan[self]), cval[lh3[self]][scan[self]]))
                                      /\ said' = (said \cup {"value"})
                                      /\ took' = (took \cup {cval[lh3[self]][scan[self]]})
                                   /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                                   /\ h0' = [h0 EXCEPT ![self] = Head(stack[self]).h0]
                                   /\ t0' = [t0 EXCEPT ![self] = Head(stack[self]).t0]
                                   /\ view' = [view EXCEPT ![self] = Head(stack[self]).view]
                                   /\ lh3' = [lh3 EXCEPT ![self] = Head(stack[self]).lh3]
                                   /\ cw' = [cw EXCEPT ![self] = Head(stack[self]).cw]
                                   /\ startTaken_' = [startTaken_ EXCEPT ![self] = Head(stack[self]).startTaken_]
                                   /\ snapped' = [snapped EXCEPT ![self] = Head(stack[self]).snapped]
                                   /\ scan' = [scan EXCEPT ![self] = Head(stack[self]).scan]
                                   /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                              ELSE /\ scan' = [scan EXCEPT ![self] = scan[self] + 1]
                                   /\ pc' = [pc EXCEPT ![self] = "PS2"]
                                   /\ UNCHANGED << cst, busy, claimsC, took, 
                                                   said, errs, stack, h0, t0, 
                                                   view, lh3, cw, startTaken_, 
                                                   snapped >>
             /\ UNCHANGED << cval, nxt, retired, freed, holders, prot, tw, hw, 
                             tptr, hptr, opn, pos, claimsP, done, rv, lh, hn, 
                             hs, lp, lh4, h1, startTaken, k, lt, w, nx, before, 
                             n >>

Pop(self) == PO1(self) \/ PO2(self) \/ PO3(self) \/ PO3w(self)
                \/ PO3v(self) \/ PO7(self) \/ PO8(self) \/ PO4(self)
                \/ PO5(self) \/ PO5w(self) \/ PO6(self) \/ PS1(self)
                \/ PS2(self)

TP1(self) == /\ pc[self] = "TP1"
             /\ /\ h1' = [h1 EXCEPT ![self] = hw]
                /\ startTaken' = [startTaken EXCEPT ![self] = took]
             /\ pc' = [pc EXCEPT ![self] = "TP2"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, rv, stack, lh, hn, hs, lp, 
                             h0, t0, view, lh3, cw, startTaken_, snapped, scan, 
                             lh4, k, lt, w, nx, before, n >>

TP2(self) == /\ pc[self] = "TP2"
             /\ IF Classify(h1[self], tw) = "empty" /\ ~MutBusyBlind
                   THEN /\ /\ errs' = (errs \cup EmptyCheck)
                           /\ said' = (said \cup {"empty"})
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lh4' = [lh4 EXCEPT ![self] = Head(stack[self]).lh4]
                        /\ h1' = [h1 EXCEPT ![self] = Head(stack[self]).h1]
                        /\ startTaken' = [startTaken EXCEPT ![self] = Head(stack[self]).startTaken]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "TP3"]
                        /\ UNCHANGED << said, errs, stack, lh4, h1, startTaken >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, rv, lh, hn, hs, lp, h0, t0, view, lh3, 
                             cw, startTaken_, snapped, scan, k, lt, w, nx, 
                             before, n >>

TP3(self) == /\ pc[self] = "TP3"
             /\ /\ busy' = [busy EXCEPT ![self] = TRUE]
                /\ lh4' = [lh4 EXCEPT ![self] = hptr]
                /\ opn' = [opn EXCEPT ![self] = IF busy[self] THEN opn[self] ELSE opn[self] + 1]
                /\ prot' = [prot EXCEPT ![self] = IF busy[self] THEN Reached(self, {hptr}) ELSE {hptr} \ retired]
             /\ pc' = [pc EXCEPT ![self] = "TP4"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, tw, hw, 
                             tptr, hptr, pos, claimsP, claimsC, took, done, 
                             said, errs, rv, stack, lh, hn, hs, lp, h0, t0, 
                             view, lh3, cw, startTaken_, snapped, scan, h1, 
                             startTaken, k, lt, w, nx, before, n >>

TP4(self) == /\ pc[self] = "TP4"
             /\ h1' = [h1 EXCEPT ![self] = hw]
             /\ pc' = [pc EXCEPT ![self] = "TP5"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, rv, stack, lh, hn, hs, lp, 
                             h0, t0, view, lh3, cw, startTaken_, snapped, scan, 
                             lh4, startTaken, k, lt, w, nx, before, n >>

TP5(self) == /\ pc[self] = "TP5"
             /\ IF ~MutBusyBlind /\ Classify(h1[self], tw) = "empty"
                   THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                           /\ errs' = (errs \cup EmptyCheck)
                           /\ said' = (said \cup {"empty"})
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lh4' = [lh4 EXCEPT ![self] = Head(stack[self]).lh4]
                        /\ h1' = [h1 EXCEPT ![self] = Head(stack[self]).h1]
                        /\ startTaken' = [startTaken EXCEPT ![self] = Head(stack[self]).startTaken]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << hs, lp >>
                   ELSE /\ IF ~MutBusyBlind /\ Classify(h1[self], tw) = "drained"
                              THEN /\ /\ hs' = [hs EXCEPT ![self] = h1[self].id]
                                      /\ lp' = [lp EXCEPT ![self] = lh4[self]]
                                      /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Drained",
                                                                               pc        |->  "TP7",
                                                                               hs        |->  hs[self],
                                                                               lp        |->  lp[self] ] >>
                                                                           \o stack[self]]
                                   /\ pc' = [pc EXCEPT ![self] = "DR1"]
                              ELSE /\ IF h1[self].id < lh4[self] \/ ~Linked(lh4[self], h1[self].id) \/ h1[self].ix >= SEG \/ WalkGone(h1[self].id)
                                         THEN /\ pc' = [pc EXCEPT ![self] = "TP3"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "TP6"]
                                   /\ UNCHANGED << stack, hs, lp >>
                        /\ UNCHANGED << busy, said, errs, lh4, h1, startTaken >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, pos, claimsP, claimsC, took, 
                             done, rv, lh, hn, h0, t0, view, lh3, cw, 
                             startTaken_, snapped, scan, k, lt, w, nx, before, 
                             n >>

TP6(self) == /\ pc[self] = "TP6"
             /\ IF cst[h1[self].id][h1[self].ix] = "EMPTY"
                   THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                           /\ errs' = (    errs \cup TouchSet(WalkSet(lh4[self], h1[self].id))
                                       \cup (IF Pos(h1[self].id, h1[self].ix) \notin claimsP THEN {"busy_unclaimed"} ELSE {}))
                           /\ said' = (said \cup {"busy"})
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lh4' = [lh4 EXCEPT ![self] = Head(stack[self]).lh4]
                        /\ h1' = [h1 EXCEPT ![self] = Head(stack[self]).h1]
                        /\ startTaken' = [startTaken EXCEPT ![self] = Head(stack[self]).startTaken]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                        /\ UNCHANGED << prot, hw, claimsC >>
                   ELSE /\ IF cst[h1[self].id][h1[self].ix] = "FULL" /\ hw = h1[self]
                              THEN /\ /\ claimsC' = (claimsC \cup {Pos(h1[self].id, h1[self].ix)})
                                      /\ errs' = (errs \cup TouchSet(WalkSet(lh4[self], h1[self].id)))
                                      /\ hw' = [hw EXCEPT !.ix = @ + 1]
                                      /\ prot' = [prot EXCEPT ![self] = Reached(self, WalkSet(lh4[self], h1[self].id))]
                                   /\ pc' = [pc EXCEPT ![self] = "TP8"]
                              ELSE /\ /\ errs' = (errs \cup TouchSet(WalkSet(lh4[self], h1[self].id)))
                                      /\ prot' = [prot EXCEPT ![self] = Reached(self, WalkSet(lh4[self], h1[self].id))]
                                   /\ pc' = [pc EXCEPT ![self] = "TP3"]
                                   /\ UNCHANGED << hw, claimsC >>
                        /\ UNCHANGED << busy, said, stack, lh4, h1, startTaken >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, tw, tptr, 
                             hptr, opn, pos, claimsP, took, done, rv, lh, hn, 
                             hs, lp, h0, t0, view, lh3, cw, startTaken_, 
                             snapped, scan, k, lt, w, nx, before, n >>

TP7(self) == /\ pc[self] = "TP7"
             /\ IF rv[self]
                   THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                           /\ rv' = [rv EXCEPT ![self] = FALSE]
                           /\ said' = (said \cup {"empty"})
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lh4' = [lh4 EXCEPT ![self] = Head(stack[self]).lh4]
                        /\ h1' = [h1 EXCEPT ![self] = Head(stack[self]).h1]
                        /\ startTaken' = [startTaken EXCEPT ![self] = Head(stack[self]).startTaken]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "TP3"]
                        /\ UNCHANGED << busy, said, rv, stack, lh4, h1, 
                                        startTaken >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, pos, claimsP, claimsC, took, 
                             done, errs, lh, hn, hs, lp, h0, t0, view, lh3, cw, 
                             startTaken_, snapped, scan, k, lt, w, nx, before, 
                             n >>

TP8(self) == /\ pc[self] = "TP8"
             /\ IF cst[h1[self].id][h1[self].ix] = "FULL"
                   THEN /\ /\ busy' = [busy EXCEPT ![self] = FALSE]
                           /\ cst' = [cst EXCEPT ![h1[self].id][h1[self].ix] = "TAKEN"]
                           /\ errs' = (       errs \cup TouchSet({h1[self].id})
                                       \cup TakeCheck(startTaken[self], Pos(h1[self].id, h1[self].ix), cval[h1[self].id][h1[self].ix]))
                           /\ said' = (said \cup {"value"})
                           /\ took' = (took \cup {cval[h1[self].id][h1[self].ix]})
                        /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                        /\ lh4' = [lh4 EXCEPT ![self] = Head(stack[self]).lh4]
                        /\ h1' = [h1 EXCEPT ![self] = Head(stack[self]).h1]
                        /\ startTaken' = [startTaken EXCEPT ![self] = Head(stack[self]).startTaken]
                        /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                   ELSE /\ errs' = (errs \cup TouchSet({h1[self].id}))
                        /\ pc' = [pc EXCEPT ![self] = "TP3"]
                        /\ UNCHANGED << cst, busy, took, said, stack, lh4, h1, 
                                        startTaken >>
             /\ UNCHANGED << cval, nxt, retired, freed, holders, prot, tw, hw, 
                             tptr, hptr, opn, pos, claimsP, claimsC, done, rv, 
                             lh, hn, hs, lp, h0, t0, view, lh3, cw, 
                             startTaken_, snapped, scan, k, lt, w, nx, before, 
                             n >>

TryPop(self) == TP1(self) \/ TP2(self) \/ TP3(self) \/ TP4(self)
                   \/ TP5(self) \/ TP6(self) \/ TP7(self) \/ TP8(self)

PU1(self) == /\ pc[self] = "PU1"
             /\ IF k[self] <= K
                   THEN /\ /\ before' = [before EXCEPT ![self] = done]
                           /\ busy' = [busy EXCEPT ![self] = TRUE]
                           /\ lt' = [lt EXCEPT ![self] = IF MutLoadLate THEN lt[self] ELSE tptr]
                           /\ opn' = [opn EXCEPT ![self] = opn[self] + 1]
                           /\ prot' = [prot EXCEPT ![self] = IF MutLoadLate THEN {} ELSE {tptr} \ retired]
                        /\ pc' = [pc EXCEPT ![self] = "PU3"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << prot, opn, busy, lt, before >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, tw, hw, 
                             tptr, hptr, pos, claimsP, claimsC, took, done, 
                             said, errs, rv, stack, lh, hn, hs, lp, h0, t0, 
                             view, lh3, cw, startTaken_, snapped, scan, lh4, 
                             h1, startTaken, k, w, nx, n >>

PU2(self) == /\ pc[self] = "PU2"
             /\ IF ~MutLoadLate
                   THEN /\ /\ lt' = [lt EXCEPT ![self] = tptr]
                           /\ prot' = [prot EXCEPT ![self] = Reached(self, {tptr})]
                   ELSE /\ TRUE
                        /\ UNCHANGED << prot, lt >>
             /\ pc' = [pc EXCEPT ![self] = "PU3"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, tw, hw, 
                             tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, rv, stack, lh, hn, hs, lp, 
                             h0, t0, view, lh3, cw, startTaken_, snapped, scan, 
                             lh4, h1, startTaken, k, w, nx, before, n >>

PU3(self) == /\ pc[self] = "PU3"
             /\ /\ claimsP' = (IF tw.ix < SEG THEN claimsP \cup {Pos(tw.id, tw.ix)} ELSE claimsP)
                /\ tw' = [tw EXCEPT !.ix = @ + 1]
                /\ w' = [w EXCEPT ![self] = tw]
             /\ IF MutLoadLate
                   THEN /\ pc' = [pc EXCEPT ![self] = "PU3m"]
                   ELSE /\ IF w'[self].ix >= SEG
                              THEN /\ pc' = [pc EXCEPT ![self] = "PU5"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "PU4"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, hw, 
                             tptr, hptr, opn, busy, pos, claimsC, took, done, 
                             said, errs, rv, stack, lh, hn, hs, lp, h0, t0, 
                             view, lh3, cw, startTaken_, snapped, scan, lh4, 
                             h1, startTaken, k, lt, nx, before, n >>

PU3m(self) == /\ pc[self] = "PU3m"
              /\ /\ lt' = [lt EXCEPT ![self] = tptr]
                 /\ prot' = [prot EXCEPT ![self] = Reached(self, {tptr})]
              /\ IF w[self].ix >= SEG
                    THEN /\ pc' = [pc EXCEPT ![self] = "PU5"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "PU4"]
              /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, tw, hw, 
                              tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                              took, done, said, errs, rv, stack, lh, hn, hs, 
                              lp, h0, t0, view, lh3, cw, startTaken_, snapped, 
                              scan, lh4, h1, startTaken, k, w, nx, before, n >>

PU4(self) == /\ pc[self] = "PU4"
             /\ IF WalkGone(w[self].id)
                   THEN /\ pc' = [pc EXCEPT ![self] = "PU2"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PU4w"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, rv, stack, lh, hn, hs, lp, 
                             h0, t0, view, lh3, cw, startTaken_, snapped, scan, 
                             lh4, h1, startTaken, k, lt, w, nx, before, n >>

PU4w(self) == /\ pc[self] = "PU4w"
              /\ /\ errs' = (    errs \cup TouchSet(WalkSet(lt[self], w[self].id))
                             
                             \cup (IF w[self].id < lt[self] \/ ~Linked(lt[self], w[self].id) THEN {"unlinked_claim"} ELSE {}))
                 /\ prot' = [prot EXCEPT ![self] = Reached(self, WalkSet(lt[self], w[self].id))]
              /\ IF w[self].id < lt[self] \/ ~Linked(lt[self], w[self].id)
                    THEN /\ pc' = [pc EXCEPT ![self] = "PU2"]
                    ELSE /\ IF w[self].id = lt[self]
                               THEN /\ pc' = [pc EXCEPT ![self] = "PU4b"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "PU4a"]
              /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, tw, hw, 
                              tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                              took, done, said, rv, stack, lh, hn, hs, lp, h0, 
                              t0, view, lh3, cw, startTaken_, snapped, scan, 
                              lh4, h1, startTaken, k, lt, w, nx, before, n >>

PU4a(self) == /\ pc[self] = "PU4a"
              /\ errs' = (errs \cup Touch(tptr, Min2(tw.id, MaxSegs - 1)))
              /\ tptr' = (IF tptr >= tw.id THEN tptr
                          ELSE LET reach == {x \in tptr .. Min2(tw.id, MaxSegs - 1) : Linked(tptr, x)}
                               IN CHOOSE x \in reach : \A y \in reach : y <= x)
              /\ pc' = [pc EXCEPT ![self] = "PU4b"]
              /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, 
                              tw, hw, hptr, opn, busy, pos, claimsP, claimsC, 
                              took, done, said, rv, stack, lh, hn, hs, lp, h0, 
                              t0, view, lh3, cw, startTaken_, snapped, scan, 
                              lh4, h1, startTaken, k, lt, w, nx, before, n >>

PU4b(self) == /\ pc[self] = "PU4b"
              /\ IF cst[w[self].id][w[self].ix] = "EMPTY"
                    THEN /\ /\ cst' = [cst EXCEPT ![w[self].id][w[self].ix] = "FULL"]
                            /\ cval' = [cval EXCEPT ![w[self].id][w[self].ix] = Val(self, k[self])]
                            /\ done' = (done \cup {Val(self, k[self])})
                            /\ errs' = (errs \cup TouchSet({w[self].id}) \cup RealTime(before[self], Pos(w[self].id, w[self].ix)))
                            /\ pos' = [pos EXCEPT ![Val(self, k[self])] = FirstPos(Val(self, k[self]), Pos(w[self].id, w[self].ix))]
                         /\ /\ before' = [before EXCEPT ![self] = {}]
                            /\ busy' = [busy EXCEPT ![self] = FALSE]
                            /\ k' = [k EXCEPT ![self] = k[self] + 1]
                            /\ lt' = [lt EXCEPT ![self] = 0]
                            /\ nx' = [nx EXCEPT ![self] = NULL]
                            /\ w' = [w EXCEPT ![self] = [id |-> 0, ix |-> 0]]
                         /\ pc' = [pc EXCEPT ![self] = "PU1"]
                    ELSE /\ IF MutRetrySame
                               THEN /\ errs' = (errs \cup TouchSet({w[self].id}))
                                    /\ pc' = [pc EXCEPT ![self] = "PU4b"]
                               ELSE /\ errs' = (errs \cup TouchSet({w[self].id}))
                                    /\ pc' = [pc EXCEPT ![self] = "PU2"]
                         /\ UNCHANGED << cst, cval, busy, pos, done, k, lt, w, 
                                         nx, before >>
              /\ UNCHANGED << nxt, retired, freed, holders, prot, tw, hw, tptr, 
                              hptr, opn, claimsP, claimsC, took, said, rv, 
                              stack, lh, hn, hs, lp, h0, t0, view, lh3, cw, 
                              startTaken_, snapped, scan, lh4, h1, startTaken, 
                              n >>

PU5(self) == /\ pc[self] = "PU5"
             /\ IF w[self].id < lt[self] \/ WalkGone(w[self].id)
                   THEN /\ IF tw.id = (w[self].id)
                              THEN /\ tw' = [id |-> (w[self].id) + 1, ix |-> 1]
                              ELSE /\ TRUE
                                   /\ tw' = tw
                        /\ pc' = [pc EXCEPT ![self] = "PU2"]
                        /\ UNCHANGED << prot, errs, nx >>
                   ELSE /\ /\ errs' = (errs \cup TouchSet(WalkSet(lt[self], w[self].id)))
                           /\ nx' = [nx EXCEPT ![self] = nxt[w[self].id]]
                           /\ prot' = [prot EXCEPT ![self] = Reached(self, WalkSet(lt[self], w[self].id))]
                        /\ pc' = [pc EXCEPT ![self] = "PU6"]
                        /\ tw' = tw
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, hw, tptr, 
                             hptr, opn, busy, pos, claimsP, claimsC, took, 
                             done, said, rv, stack, lh, hn, hs, lp, h0, t0, 
                             view, lh3, cw, startTaken_, snapped, scan, lh4, 
                             h1, startTaken, k, lt, w, before, n >>

PU6(self) == /\ pc[self] = "PU6"
             /\ IF nx[self] = NULL /\ nxt[w[self].id] = NULL /\ w[self].id + 1 >= MaxSegs
                   THEN /\ errs' = (errs \cup {"bound"})
                        /\ /\ before' = [before EXCEPT ![self] = {}]
                           /\ busy' = [busy EXCEPT ![self] = FALSE]
                           /\ k' = [k EXCEPT ![self] = k[self] + 1]
                           /\ lt' = [lt EXCEPT ![self] = 0]
                           /\ nx' = [nx EXCEPT ![self] = NULL]
                           /\ w' = [w EXCEPT ![self] = [id |-> 0, ix |-> 0]]
                        /\ pc' = [pc EXCEPT ![self] = "PU1"]
                        /\ UNCHANGED << cst, cval, nxt, pos, claimsP >>
                   ELSE /\ IF nx[self] = NULL /\ nxt[w[self].id] = NULL
                              THEN /\ /\ claimsP' = (claimsP \cup {Pos(w[self].id + 1, 0)})
                                      /\ cst' = [cst EXCEPT ![w[self].id + 1][0] = "FULL"]
                                      /\ cval' = [cval EXCEPT ![w[self].id + 1][0] = Val(self, k[self])]
                                      /\ errs' = (errs \cup TouchSet({w[self].id}) \cup RealTime(before[self], Pos(w[self].id + 1, 0)))
                                      /\ nx' = [nx EXCEPT ![self] = w[self].id + 1]
                                      /\ nxt' = [nxt EXCEPT ![w[self].id] = w[self].id + 1]
                                      /\ pos' = [pos EXCEPT ![Val(self, k[self])] = FirstPos(Val(self, k[self]), Pos(w[self].id + 1, 0))]
                              ELSE /\ IF nx[self] = NULL
                                         THEN /\ /\ errs' = (errs \cup TouchSet({w[self].id}))
                                                 /\ nx' = [nx EXCEPT ![self] = nxt[w[self].id]]
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << errs, nx >>
                                   /\ UNCHANGED << cst, cval, nxt, pos, 
                                                   claimsP >>
                        /\ pc' = [pc EXCEPT ![self] = "PU7"]
                        /\ UNCHANGED << busy, k, lt, w, before >>
             /\ UNCHANGED << retired, freed, holders, prot, tw, hw, tptr, hptr, 
                             opn, claimsC, took, done, said, rv, stack, lh, hn, 
                             hs, lp, h0, t0, view, lh3, cw, startTaken_, 
                             snapped, scan, lh4, h1, startTaken, n >>

PU7(self) == /\ pc[self] = "PU7"
             /\ IF MutStoreAdvance /\ tw.id = w[self].id
                   THEN /\ pc' = [pc EXCEPT ![self] = "PU7s"]
                        /\ tw' = tw
                   ELSE /\ IF tw.id = (w[self].id)
                              THEN /\ tw' = [id |-> (w[self].id) + 1, ix |-> 1]
                              ELSE /\ TRUE
                                   /\ tw' = tw
                        /\ pc' = [pc EXCEPT ![self] = "PU8"]
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, hw, 
                             tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, rv, stack, lh, hn, hs, lp, 
                             h0, t0, view, lh3, cw, startTaken_, snapped, scan, 
                             lh4, h1, startTaken, k, lt, w, nx, before, n >>

PU7s(self) == /\ pc[self] = "PU7s"
              /\ tw' = [id |-> w[self].id + 1, ix |-> 1]
              /\ pc' = [pc EXCEPT ![self] = "PU8"]
              /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, 
                              hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                              took, done, said, errs, rv, stack, lh, hn, hs, 
                              lp, h0, t0, view, lh3, cw, startTaken_, snapped, 
                              scan, lh4, h1, startTaken, k, lt, w, nx, before, 
                              n >>

PU8(self) == /\ pc[self] = "PU8"
             /\ IF lt[self] = w[self].id
                   THEN /\ IF tptr = lt[self]
                              THEN /\ tptr' = nx[self]
                              ELSE /\ TRUE
                                   /\ tptr' = tptr
                        /\ errs' = errs
                   ELSE /\ errs' = (errs \cup Touch(tptr, Min2(tw.id, MaxSegs - 1)))
                        /\ tptr' = (IF tptr >= tw.id THEN tptr
                                    ELSE LET reach == {x \in tptr .. Min2(tw.id, MaxSegs - 1) : Linked(tptr, x)}
                                         IN CHOOSE x \in reach : \A y \in reach : y <= x)
             /\ IF pos[Val(self, k[self])] # NULL /\ ~MutLinkRetry
                   THEN /\ done' = (done \cup {Val(self, k[self])})
                        /\ /\ before' = [before EXCEPT ![self] = {}]
                           /\ busy' = [busy EXCEPT ![self] = FALSE]
                           /\ k' = [k EXCEPT ![self] = k[self] + 1]
                           /\ lt' = [lt EXCEPT ![self] = 0]
                           /\ nx' = [nx EXCEPT ![self] = NULL]
                           /\ w' = [w EXCEPT ![self] = [id |-> 0, ix |-> 0]]
                        /\ pc' = [pc EXCEPT ![self] = "PU1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "PU2"]
                        /\ UNCHANGED << busy, done, k, lt, w, nx, before >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, hptr, opn, pos, claimsP, claimsC, took, said, 
                             rv, stack, lh, hn, hs, lp, h0, t0, view, lh3, cw, 
                             startTaken_, snapped, scan, lh4, h1, startTaken, 
                             n >>

Producer(self) == PU1(self) \/ PU2(self) \/ PU3(self) \/ PU3m(self)
                     \/ PU4(self) \/ PU4w(self) \/ PU4a(self) \/ PU4b(self)
                     \/ PU5(self) \/ PU6(self) \/ PU7(self) \/ PU7s(self)
                     \/ PU8(self)

CO1(self) == /\ pc[self] = "CO1"
             /\ IF n[self] < Pops
                   THEN /\ n' = [n EXCEPT ![self] = n[self] + 1]
                        /\ IF Try
                              THEN /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "TryPop",
                                                                            pc        |->  "CO1",
                                                                            lh4       |->  lh4[self],
                                                                            h1        |->  h1[self],
                                                                            startTaken |->  startTaken[self] ] >>
                                                                        \o stack[self]]
                                   /\ lh4' = [lh4 EXCEPT ![self] = 0]
                                   /\ h1' = [h1 EXCEPT ![self] = [id |-> 0, ix |-> 0]]
                                   /\ startTaken' = [startTaken EXCEPT ![self] = {}]
                                   /\ pc' = [pc EXCEPT ![self] = "TP1"]
                                   /\ UNCHANGED << h0, t0, view, lh3, cw, 
                                                   startTaken_, snapped, scan >>
                              ELSE /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Pop",
                                                                            pc        |->  "CO1",
                                                                            h0        |->  h0[self],
                                                                            t0        |->  t0[self],
                                                                            view      |->  view[self],
                                                                            lh3       |->  lh3[self],
                                                                            cw        |->  cw[self],
                                                                            startTaken_ |->  startTaken_[self],
                                                                            snapped   |->  snapped[self],
                                                                            scan      |->  scan[self] ] >>
                                                                        \o stack[self]]
                                   /\ h0' = [h0 EXCEPT ![self] = [id |-> 0, ix |-> 0]]
                                   /\ t0' = [t0 EXCEPT ![self] = [id |-> 0, ix |-> 0]]
                                   /\ view' = [view EXCEPT ![self] = ""]
                                   /\ lh3' = [lh3 EXCEPT ![self] = 0]
                                   /\ cw' = [cw EXCEPT ![self] = [id |-> 0, ix |-> 0]]
                                   /\ startTaken_' = [startTaken_ EXCEPT ![self] = {}]
                                   /\ snapped' = [snapped EXCEPT ![self] = FALSE]
                                   /\ scan' = [scan EXCEPT ![self] = 0]
                                   /\ pc' = [pc EXCEPT ![self] = "PO1"]
                                   /\ UNCHANGED << lh4, h1, startTaken >>
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << stack, h0, t0, view, lh3, cw, 
                                        startTaken_, snapped, scan, lh4, h1, 
                                        startTaken, n >>
             /\ UNCHANGED << cst, cval, nxt, retired, freed, holders, prot, tw, 
                             hw, tptr, hptr, opn, busy, pos, claimsP, claimsC, 
                             took, done, said, errs, rv, lh, hn, hs, lp, k, lt, 
                             w, nx, before >>

Consumer(self) == CO1(self)

RC1 == /\ pc[0] = "RC1"
       /\ IF ~AllDone
             THEN /\ \E s \in {x \in retired \ freed :
                               \A h \in holders[x] : opn[h[1]] # h[2] \/ ~busy[h[1]]}:
                       freed' = (freed \cup {s})
                  /\ pc' = [pc EXCEPT ![0] = "RC1"]
             ELSE /\ pc' = [pc EXCEPT ![0] = "Done"]
                  /\ freed' = freed
       /\ UNCHANGED << cst, cval, nxt, retired, holders, prot, tw, hw, tptr, 
                       hptr, opn, busy, pos, claimsP, claimsC, took, done, 
                       said, errs, rv, stack, lh, hn, hs, lp, h0, t0, view, 
                       lh3, cw, startTaken_, snapped, scan, lh4, h1, 
                       startTaken, k, lt, w, nx, before, n >>

Reclaimer == RC1

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == Reclaimer
           \/ (\E self \in ProcSet:  \/ CatchUpHead(self) \/ Drained(self)
                                     \/ Pop(self) \/ TryPop(self))
           \/ (\E self \in Producers: Producer(self))
           \/ (\E self \in Consumers: Consumer(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
