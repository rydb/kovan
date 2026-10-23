----------------------------- MODULE MC_SegQueue -----------------------------
(***************************************************************************)
(* The properties checked of SegQueue.tla, and the fair specification.     *)
(***************************************************************************)
EXTENDS SegQueue

\* No thread touches a segment kovan freed.
NoUseAfterFree == "uaf" \notin errs
\* A claim never names a segment its walk cannot reach: the `debug_assert!` path is unreachable.
NoUnlinkedClaim == "unlinked_claim" \notin errs
\* The configuration's segment bound is never what stopped a push.
NoBound == "bound" \notin errs
\* A pop that answers None began after every push that had returned had its cell claimed by a
\* pop: the queue was empty at some moment of the call.
EmptySound == "empty_unsound" \notin errs
\* try_pop answers Busy only for a cell a push claimed and has not written yet.
BusyMeansClaimed == "busy_unclaimed" \notin errs

\* The head word is at most one segment ahead of the tail word, and only once the tail word passed
\* its segment's end (the linking push claimed past it): the hypothesis of the Lean theorem that
\* `classify` on the code's wrapped ids answers as on ids counted without wrapping.
Words == hw.id <= tw.id + 1 /\ (hw.id = tw.id + 1 => tw.ix > SEG)

\* No value is taken twice.
UniqueTake == "dup" \notin errs
\* A push that began after another returned writes its value behind it: the queue order is
\* consistent with real time (so one producer's values sit in the order it pushed them).
RealTimeOrder == "rt_order" \notin errs
\* A pop takes a value behind every value taken before it began (so each consumer takes values
\* in queue order).
PopOrder == "pop_order" \notin errs
\* When every thread is done, every value pushed was taken, or is still in its cell at or past the
\* head, where a later pop would take it: nothing pushed is lost.
HeadPos == hw.id * SEG + Min2(hw.ix, SEG)
NoLoss ==
    AllDone => \A x \in done :
        \/ x \in took
        \/ cst[pos[x] \div SEG][pos[x] % SEG] = "FULL" /\ pos[x] >= HeadPos

\* Every thread's steps taken fairly: an operation that can go on does. (Termination, every
\* process ending, is the translation's.)
ThreadStep(t) ==
    IF t \in Producers THEN Producer(t)
    ELSE CatchUpHead(t) \/ Drained(t) \/ Pop(t) \/ TryPop(t) \/ Consumer(t)
FairSpec == Spec /\ WF_vars(Reclaimer) /\ \A t \in Threads : WF_vars(ThreadStep(t))

\* Witnesses: each says a case never happens, so a counterexample proves the passing
\* configurations reach it.
NoLinkW == nxt[0] = NULL
NoPoisonW == \A s \in Segs : \A i \in Cells : cst[s][i] = "TAKEN" => cval[s][i] # 0
NoBusyW == "busy" \notin said
NoFreeW == freed = {}
NoEmptyAnswerW == said \cap {"none", "empty"} = {}
NoHeadAheadW == hw.id # tw.id + 1
=============================================================================
