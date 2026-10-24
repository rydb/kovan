-------------------------------- MODULE Slab --------------------------------
(***************************************************************************)
(* The slab layer under kovan's magazine cache (kovan/src/recycle/slab.rs), *)
(* for one class, at the grain of its atomic steps.                        *)
(*                                                                          *)
(* One owner thread carves blocks from chunks of CAP blocks it makes, hands *)
(* some to releaser threads (the nodes of a structure other threads free),  *)
(* and gives the rest back to its own chunks. A releaser gives a block back *)
(* by pushing it on the owner's inbox with a compare-and-swap; the owner    *)
(* drains the inbox when it has no chunk with a block to hand out, before   *)
(* it would make a new chunk. When a chunk's last block comes back, the     *)
(* owner frees it, keeping one empty chunk as a spare.                      *)
(*                                                                          *)
(* The owner then exits: it drains the inbox, writes into each chunk the    *)
(* count of its blocks still out (freeing the empty ones), and closes the   *)
(* inbox with a swap, counting down for the blocks pushed in between. A     *)
(* releaser that finds the inbox closed counts down instead; whoever brings *)
(* a chunk's count to zero frees it. The inbox is freed with its last       *)
(* reference: the owner's and one per chunk.                                *)
(*                                                                          *)
(* A releaser holds a block of the chunk it touches, so it may read the     *)
(* chunk (for its inbox) and the inbox; once its push or its count-down is  *)
(* done, it touches neither. Every access is checked against the chunks and *)
(* the inbox already freed.                                                 *)
(*                                                                          *)
(* `Mutation` puts back one wrong rule at a time; see README.md.            *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Releasers,  \* thread ids the owner hands blocks to
    Ops,        \* operations the owner runs before it exits
    CAP,        \* blocks a chunk holds
    NChunks,    \* chunks the owner can make
    Mutation    \* "none", or one wrong rule put back

Owner == 0
Chunks == 1 .. NChunks
Blocks == Chunks \X (0 .. CAP - 1)
NULL == <<0, 0>>

\* close_before_counts: the exiting owner closes the inbox before it writes the chunks' counts,
\* so a releaser can count down from the old count (CountsRight catches it).
MutCloseFirst == Mutation = "close_before_counts"
\* touch_after_push: a releaser reads the block's chunk after its push handed the block back,
\* when the owner may already have freed the chunk (NoUseAfterFree catches it).
MutTouchAfter == Mutation = "touch_after_push"
\* drop_closed_blocks: the exiting owner's close drops the blocks pushed before it instead of
\* counting them down (BlockOnce catches the blocks no one has).
MutDropClosed == Mutation = "drop_closed_blocks"
\* free_one_early: the owner frees a chunk when one block is still out (UsedRight catches the
\* block of a freed chunk).
MutFreeEarly == Mutation = "free_one_early"
\* stale_head: a releaser whose compare-and-swap failed retries with the head it read before,
\* forever (Termination catches it).
MutStaleHead == Mutation = "stale_head"
\* keep_inbox_ref: freeing a chunk does not give up its reference to the inbox, which is then
\* never freed (NoLeak catches it).
MutKeepRef == Mutation = "keep_inbox_ref"
\* What freeing a chunk does to the inbox's references.
RefDrop == IF MutKeepRef THEN 0 ELSE 1

(* --algorithm Slab
variables
    \* the chunks made, the ones freed, and each one's owner-side words
    made = {},
    freed = {},
    carved = [c \in Chunks |-> 0],
    used = [c \in Chunks |-> 0],
    local = [c \in Chunks |-> {}],
    partial = {},
    spare = 0,
    \* once the owner exited: each chunk's count of blocks out (-1: not written yet)
    outstanding = [c \in Chunks |-> -1],
    \* the inbox: its blocks, whether closed, a version for compare-and-swap, its references
    inbox = <<>>,
    closed = FALSE,
    ver = 0,
    refs = 1,
    inboxFreed = FALSE,
    \* who holds which block
    held = [t \in Releasers \cup {Owner} |-> {}],
    \* blocks the exiting owner's close collected and has not counted down yet, and the
    \* blocks counted back into their orphaned chunks
    collected = <<>>,
    returned = {},
    errs = {};

define
    ChunkOf(b) == b[1]
    \* Touching chunk c (or the inbox): a freed one is a use after free.
    Touch(c) == IF c \in freed THEN {"uaf"} ELSE {}
    TouchInbox == IF inboxFreed THEN {"uaf"} ELSE {}
    Range(s) == {s[i] : i \in DOMAIN s}
end define;

\* ---------------------------------------------------------------- the owner's helpers
\* settle: a chunk got a block back; free it if that emptied it and a spare is kept already,
\* else keep it as the spare (if empty) and list it as having blocks to hand out.
macro Settle(c)
begin
    if (used[c] = 0 \/ (MutFreeEarly /\ used[c] = 1)) /\ spare # 0 /\ spare # c then
        freed := freed \cup {c} || partial := partial \ {c} || refs := refs - RefDrop;
    else
        spare := IF used[c] = 0 THEN c ELSE spare || partial := partial \cup {c};
    end if;
end macro;

\* ---------------------------------------------------------------- the owner
process TheOwner = Owner
variables k = 0, ob = NULL;
begin
OW1:
    while k < Ops do
        k := k + 1;
        either
            \* alloc: a block from a chunk with one to hand out
            await partial # {};
            with ch \in partial do
                if local[ch] # {} then
                    with x \in local[ch] do
                        local[ch] := local[ch] \ {x} || used[ch] := used[ch] + 1
                            || held[Owner] := held[Owner] \cup {x}
                            || spare := IF spare = ch THEN 0 ELSE spare;
                    end with;
                elsif carved[ch] < CAP then
                    carved[ch] := carved[ch] + 1 || used[ch] := used[ch] + 1
                        || held[Owner] := held[Owner] \cup {<<ch, carved[ch]>>}
                        || spare := IF spare = ch THEN 0 ELSE spare;
                else
                    partial := partial \ {ch};
                end if;
            end with;
        or
            \* alloc with no chunk to take from: drain the inbox, or make a chunk
            await partial = {};
            if inbox # <<>> then
                \* the swap; each block goes back to its chunk's free list
                inbox := <<>> || ver := ver + 1 || collected := inbox;
                goto OW2;
            elsif Chunks \ made # {} then
                with ch \in Chunks \ made do
                    made := made \cup {ch} || partial := partial \cup {ch} || refs := refs + 1;
                end with;
            end if;
        or
            \* hand a block to a releaser
            with x \in held[Owner], r \in Releasers do
                held[Owner] := held[Owner] \ {x} || held[r] := held[r] \cup {x};
            end with;
        or
            \* give a block back to its own chunk
            with x \in held[Owner] do
                held[Owner] := held[Owner] \ {x} || local[ChunkOf(x)] := local[ChunkOf(x)] \cup {x}
                    || used[ChunkOf(x)] := used[ChunkOf(x)] - 1 || ob := x;
            end with;
            goto OW3;
        end either;
    end while;
    goto EX1;
OW2: \* the drained blocks, one by one, back to their chunks
    while collected # <<>> do
        ob := Head(collected);
        local[ChunkOf(ob)] := local[ChunkOf(ob)] \cup {ob} || used[ChunkOf(ob)] := used[ChunkOf(ob)] - 1
            || collected := Tail(collected) || errs := errs \cup Touch(ChunkOf(ob));
OW2s:
        Settle(ChunkOf(ob));
    end while;
    goto OW1;
OW3:
    Settle(ChunkOf(ob));
    goto OW1;
\* ---------------------------------------------------------------- the owner's exit
EX1: \* the blocks it still holds go back, then the inbox is drained
    while held[Owner] # {} do
        with x \in held[Owner] do
            held[Owner] := held[Owner] \ {x} || local[ChunkOf(x)] := local[ChunkOf(x)] \cup {x}
                || used[ChunkOf(x)] := used[ChunkOf(x)] - 1;
        end with;
    end while;
EX2:
    if MutCloseFirst then
        goto EX4;
    else
        collected := inbox || inbox := <<>> || ver := ver + 1;
    end if;
EX2b:
    while collected # <<>> do
        local[ChunkOf(Head(collected))] := local[ChunkOf(Head(collected))] \cup {Head(collected)}
            || used[ChunkOf(Head(collected))] := used[ChunkOf(Head(collected))] - 1
            || collected := Tail(collected);
    end while;
EX3: \* every empty chunk freed, every other one's count written
    freed := freed \cup {ch \in made \ freed : used[ch] = 0}
        || refs := refs - RefDrop * Cardinality({ch \in made \ freed : used[ch] = 0})
        || outstanding := [ch \in Chunks |->
               IF ch \in made \ freed /\ used[ch] > 0 THEN used[ch] ELSE outstanding[ch]];
    if MutCloseFirst then goto EX6; end if;
EX4: \* the close: a swap that collects the blocks pushed since the drain
    collected := IF MutDropClosed THEN <<>> ELSE inbox || inbox := <<>> || closed := TRUE
        || ver := ver + 1;
    if MutCloseFirst then goto EX2b; end if;
EX5: \* each collected block counted down
    while collected # <<>> do
        errs := errs \cup Touch(ChunkOf(Head(collected)))
            || outstanding[ChunkOf(Head(collected))] := outstanding[ChunkOf(Head(collected))] - 1
            || freed := IF outstanding[ChunkOf(Head(collected))] = 1
                        THEN freed \cup {ChunkOf(Head(collected))} ELSE freed
            || refs := IF outstanding[ChunkOf(Head(collected))] = 1 THEN refs - RefDrop ELSE refs
            || returned := returned \cup {Head(collected)}
            || collected := Tail(collected);
    end while;
EX6: \* the owner's reference to the inbox
    refs := refs - 1 || inboxFreed := inboxFreed \/ refs = 1;
end process;

\* ---------------------------------------------------------------- the releasers
process Releaser \in Releasers
variables rb = NULL, head = [v |-> 0, shut |-> FALSE];
begin
RR0:
    while ~(held[self] = {} /\ pc[Owner] = "Done") do
        await held[self] # {};
        with x \in held[self] do
            rb := x || held[self] := held[self] \ {x};
        end with;
RR1: \* the block's chunk, for its inbox; the inbox's word
        errs := errs \cup Touch(ChunkOf(rb)) \cup TouchInbox || head := [v |-> ver, shut |-> closed];
RR2: \* closed: count down; else the compare-and-swap, which on failure answers the word now
        if head.shut then
            goto RR4;
        elsif ver = head.v then
            errs := errs \cup TouchInbox || inbox := Append(inbox, rb) || ver := ver + 1;
            if MutTouchAfter then goto RR3; else goto RR0; end if;
        else
            errs := errs \cup TouchInbox
                || head := IF MutStaleHead THEN head ELSE [v |-> ver, shut |-> closed];
            goto RR2;
        end if;
RR3: \* (touch_after_push) the chunk read again
        errs := errs \cup Touch(ChunkOf(rb));
        goto RR0;
RR4: \* the count-down; the last block back frees the chunk, and maybe the inbox
        errs := errs \cup Touch(ChunkOf(rb))
            || outstanding[ChunkOf(rb)] := outstanding[ChunkOf(rb)] - 1
            || freed := IF outstanding[ChunkOf(rb)] = 1 THEN freed \cup {ChunkOf(rb)} ELSE freed
            || refs := IF outstanding[ChunkOf(rb)] = 1 THEN refs - RefDrop ELSE refs
            || inboxFreed := inboxFreed \/ (outstanding[ChunkOf(rb)] = 1 /\ refs - RefDrop = 0)
            || returned := returned \cup {rb};
    end while;
end process;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "5926e7e3" /\ chksum(tla) = "6ff52cc2")
VARIABLES made, freed, carved, used, local, partial, spare, outstanding, 
          inbox, closed, ver, refs, inboxFreed, held, collected, returned, 
          errs, pc

(* define statement *)
ChunkOf(b) == b[1]

Touch(c) == IF c \in freed THEN {"uaf"} ELSE {}
TouchInbox == IF inboxFreed THEN {"uaf"} ELSE {}
Range(s) == {s[i] : i \in DOMAIN s}

VARIABLES k, ob, rb, head

vars == << made, freed, carved, used, local, partial, spare, outstanding, 
           inbox, closed, ver, refs, inboxFreed, held, collected, returned, 
           errs, pc, k, ob, rb, head >>

ProcSet == {Owner} \cup (Releasers)

Init == (* Global variables *)
        /\ made = {}
        /\ freed = {}
        /\ carved = [c \in Chunks |-> 0]
        /\ used = [c \in Chunks |-> 0]
        /\ local = [c \in Chunks |-> {}]
        /\ partial = {}
        /\ spare = 0
        /\ outstanding = [c \in Chunks |-> -1]
        /\ inbox = <<>>
        /\ closed = FALSE
        /\ ver = 0
        /\ refs = 1
        /\ inboxFreed = FALSE
        /\ held = [t \in Releasers \cup {Owner} |-> {}]
        /\ collected = <<>>
        /\ returned = {}
        /\ errs = {}
        (* Process TheOwner *)
        /\ k = 0
        /\ ob = NULL
        (* Process Releaser *)
        /\ rb = [self \in Releasers |-> NULL]
        /\ head = [self \in Releasers |-> [v |-> 0, shut |-> FALSE]]
        /\ pc = [self \in ProcSet |-> CASE self = Owner -> "OW1"
                                        [] self \in Releasers -> "RR0"]

OW1 == /\ pc[Owner] = "OW1"
       /\ IF k < Ops
             THEN /\ k' = k + 1
                  /\ \/ /\ partial # {}
                        /\ \E ch \in partial:
                             IF local[ch] # {}
                                THEN /\ \E x \in local[ch]:
                                          /\ held' = [held EXCEPT ![Owner] = held[Owner] \cup {x}]
                                          /\ local' = [local EXCEPT ![ch] = local[ch] \ {x}]
                                          /\ spare' = (IF spare = ch THEN 0 ELSE spare)
                                          /\ used' = [used EXCEPT ![ch] = used[ch] + 1]
                                     /\ UNCHANGED << carved, partial >>
                                ELSE /\ IF carved[ch] < CAP
                                           THEN /\ /\ carved' = [carved EXCEPT ![ch] = carved[ch] + 1]
                                                   /\ held' = [held EXCEPT ![Owner] = held[Owner] \cup {<<ch, carved[ch]>>}]
                                                   /\ spare' = (IF spare = ch THEN 0 ELSE spare)
                                                   /\ used' = [used EXCEPT ![ch] = used[ch] + 1]
                                                /\ UNCHANGED partial
                                           ELSE /\ partial' = partial \ {ch}
                                                /\ UNCHANGED << carved, used, 
                                                                spare, held >>
                                     /\ local' = local
                        /\ pc' = [pc EXCEPT ![Owner] = "OW1"]
                        /\ UNCHANGED <<made, inbox, ver, refs, collected, ob>>
                     \/ /\ partial = {}
                        /\ IF inbox # <<>>
                              THEN /\ /\ collected' = inbox
                                      /\ inbox' = <<>>
                                      /\ ver' = ver + 1
                                   /\ pc' = [pc EXCEPT ![Owner] = "OW2"]
                                   /\ UNCHANGED << made, partial, refs >>
                              ELSE /\ IF Chunks \ made # {}
                                         THEN /\ \E ch \in Chunks \ made:
                                                   /\ made' = (made \cup {ch})
                                                   /\ partial' = (partial \cup {ch})
                                                   /\ refs' = refs + 1
                                         ELSE /\ TRUE
                                              /\ UNCHANGED << made, partial, 
                                                              refs >>
                                   /\ pc' = [pc EXCEPT ![Owner] = "OW1"]
                                   /\ UNCHANGED << inbox, ver, collected >>
                        /\ UNCHANGED <<carved, used, local, spare, held, ob>>
                     \/ /\ \E x \in held[Owner]:
                             \E r \in Releasers:
                               held' = [held EXCEPT ![Owner] = held[Owner] \ {x},
                                                    ![r] = held[r] \cup {x}]
                        /\ pc' = [pc EXCEPT ![Owner] = "OW1"]
                        /\ UNCHANGED <<made, carved, used, local, partial, spare, inbox, ver, refs, collected, ob>>
                     \/ /\ \E x \in held[Owner]:
                             /\ held' = [held EXCEPT ![Owner] = held[Owner] \ {x}]
                             /\ local' = [local EXCEPT ![ChunkOf(x)] = local[ChunkOf(x)] \cup {x}]
                             /\ ob' = x
                             /\ used' = [used EXCEPT ![ChunkOf(x)] = used[ChunkOf(x)] - 1]
                        /\ pc' = [pc EXCEPT ![Owner] = "OW3"]
                        /\ UNCHANGED <<made, carved, partial, spare, inbox, ver, refs, collected>>
             ELSE /\ pc' = [pc EXCEPT ![Owner] = "EX1"]
                  /\ UNCHANGED << made, carved, used, local, partial, spare, 
                                  inbox, ver, refs, held, collected, k, ob >>
       /\ UNCHANGED << freed, outstanding, closed, inboxFreed, returned, errs, 
                       rb, head >>

OW2 == /\ pc[Owner] = "OW2"
       /\ IF collected # <<>>
             THEN /\ ob' = Head(collected)
                  /\ /\ collected' = Tail(collected)
                     /\ errs' = (errs \cup Touch(ChunkOf(ob')))
                     /\ local' = [local EXCEPT ![ChunkOf(ob')] = local[ChunkOf(ob')] \cup {ob'}]
                     /\ used' = [used EXCEPT ![ChunkOf(ob')] = used[ChunkOf(ob')] - 1]
                  /\ pc' = [pc EXCEPT ![Owner] = "OW2s"]
             ELSE /\ pc' = [pc EXCEPT ![Owner] = "OW1"]
                  /\ UNCHANGED << used, local, collected, errs, ob >>
       /\ UNCHANGED << made, freed, carved, partial, spare, outstanding, inbox, 
                       closed, ver, refs, inboxFreed, held, returned, k, rb, 
                       head >>

OW2s == /\ pc[Owner] = "OW2s"
        /\ IF (used[(ChunkOf(ob))] = 0 \/ (MutFreeEarly /\ used[(ChunkOf(ob))] = 1)) /\ spare # 0 /\ spare # (ChunkOf(ob))
              THEN /\ /\ freed' = (freed \cup {(ChunkOf(ob))})
                      /\ partial' = partial \ {(ChunkOf(ob))}
                      /\ refs' = refs - RefDrop
                   /\ spare' = spare
              ELSE /\ /\ partial' = (partial \cup {(ChunkOf(ob))})
                      /\ spare' = (IF used[(ChunkOf(ob))] = 0 THEN (ChunkOf(ob)) ELSE spare)
                   /\ UNCHANGED << freed, refs >>
        /\ pc' = [pc EXCEPT ![Owner] = "OW2"]
        /\ UNCHANGED << made, carved, used, local, outstanding, inbox, closed, 
                        ver, inboxFreed, held, collected, returned, errs, k, 
                        ob, rb, head >>

OW3 == /\ pc[Owner] = "OW3"
       /\ IF (used[(ChunkOf(ob))] = 0 \/ (MutFreeEarly /\ used[(ChunkOf(ob))] = 1)) /\ spare # 0 /\ spare # (ChunkOf(ob))
             THEN /\ /\ freed' = (freed \cup {(ChunkOf(ob))})
                     /\ partial' = partial \ {(ChunkOf(ob))}
                     /\ refs' = refs - RefDrop
                  /\ spare' = spare
             ELSE /\ /\ partial' = (partial \cup {(ChunkOf(ob))})
                     /\ spare' = (IF used[(ChunkOf(ob))] = 0 THEN (ChunkOf(ob)) ELSE spare)
                  /\ UNCHANGED << freed, refs >>
       /\ pc' = [pc EXCEPT ![Owner] = "OW1"]
       /\ UNCHANGED << made, carved, used, local, outstanding, inbox, closed, 
                       ver, inboxFreed, held, collected, returned, errs, k, ob, 
                       rb, head >>

EX1 == /\ pc[Owner] = "EX1"
       /\ IF held[Owner] # {}
             THEN /\ \E x \in held[Owner]:
                       /\ held' = [held EXCEPT ![Owner] = held[Owner] \ {x}]
                       /\ local' = [local EXCEPT ![ChunkOf(x)] = local[ChunkOf(x)] \cup {x}]
                       /\ used' = [used EXCEPT ![ChunkOf(x)] = used[ChunkOf(x)] - 1]
                  /\ pc' = [pc EXCEPT ![Owner] = "EX1"]
             ELSE /\ pc' = [pc EXCEPT ![Owner] = "EX2"]
                  /\ UNCHANGED << used, local, held >>
       /\ UNCHANGED << made, freed, carved, partial, spare, outstanding, inbox, 
                       closed, ver, refs, inboxFreed, collected, returned, 
                       errs, k, ob, rb, head >>

EX2 == /\ pc[Owner] = "EX2"
       /\ IF MutCloseFirst
             THEN /\ pc' = [pc EXCEPT ![Owner] = "EX4"]
                  /\ UNCHANGED << inbox, ver, collected >>
             ELSE /\ /\ collected' = inbox
                     /\ inbox' = <<>>
                     /\ ver' = ver + 1
                  /\ pc' = [pc EXCEPT ![Owner] = "EX2b"]
       /\ UNCHANGED << made, freed, carved, used, local, partial, spare, 
                       outstanding, closed, refs, inboxFreed, held, returned, 
                       errs, k, ob, rb, head >>

EX2b == /\ pc[Owner] = "EX2b"
        /\ IF collected # <<>>
              THEN /\ /\ collected' = Tail(collected)
                      /\ local' = [local EXCEPT ![ChunkOf(Head(collected))] = local[ChunkOf(Head(collected))] \cup {Head(collected)}]
                      /\ used' = [used EXCEPT ![ChunkOf(Head(collected))] = used[ChunkOf(Head(collected))] - 1]
                   /\ pc' = [pc EXCEPT ![Owner] = "EX2b"]
              ELSE /\ pc' = [pc EXCEPT ![Owner] = "EX3"]
                   /\ UNCHANGED << used, local, collected >>
        /\ UNCHANGED << made, freed, carved, partial, spare, outstanding, 
                        inbox, closed, ver, refs, inboxFreed, held, returned, 
                        errs, k, ob, rb, head >>

EX3 == /\ pc[Owner] = "EX3"
       /\ /\ freed' = (freed \cup {ch \in made \ freed : used[ch] = 0})
          /\ outstanding' =            [ch \in Chunks |->
                            IF ch \in made \ freed /\ used[ch] > 0 THEN used[ch] ELSE outstanding[ch]]
          /\ refs' = refs - RefDrop * Cardinality({ch \in made \ freed : used[ch] = 0})
       /\ IF MutCloseFirst
             THEN /\ pc' = [pc EXCEPT ![Owner] = "EX6"]
             ELSE /\ pc' = [pc EXCEPT ![Owner] = "EX4"]
       /\ UNCHANGED << made, carved, used, local, partial, spare, inbox, 
                       closed, ver, inboxFreed, held, collected, returned, 
                       errs, k, ob, rb, head >>

EX4 == /\ pc[Owner] = "EX4"
       /\ /\ closed' = TRUE
          /\ collected' = IF MutDropClosed THEN <<>> ELSE inbox
          /\ inbox' = <<>>
          /\ ver' = ver + 1
       /\ IF MutCloseFirst
             THEN /\ pc' = [pc EXCEPT ![Owner] = "EX2b"]
             ELSE /\ pc' = [pc EXCEPT ![Owner] = "EX5"]
       /\ UNCHANGED << made, freed, carved, used, local, partial, spare, 
                       outstanding, refs, inboxFreed, held, returned, errs, k, 
                       ob, rb, head >>

EX5 == /\ pc[Owner] = "EX5"
       /\ IF collected # <<>>
             THEN /\ /\ collected' = Tail(collected)
                     /\ errs' = (errs \cup Touch(ChunkOf(Head(collected))))
                     /\ freed' = (IF outstanding[ChunkOf(Head(collected))] = 1
                                  THEN freed \cup {ChunkOf(Head(collected))} ELSE freed)
                     /\ outstanding' = [outstanding EXCEPT ![ChunkOf(Head(collected))] = outstanding[ChunkOf(Head(collected))] - 1]
                     /\ refs' = (IF outstanding[ChunkOf(Head(collected))] = 1 THEN refs - RefDrop ELSE refs)
                     /\ returned' = (returned \cup {Head(collected)})
                  /\ pc' = [pc EXCEPT ![Owner] = "EX5"]
             ELSE /\ pc' = [pc EXCEPT ![Owner] = "EX6"]
                  /\ UNCHANGED << freed, outstanding, refs, collected, 
                                  returned, errs >>
       /\ UNCHANGED << made, carved, used, local, partial, spare, inbox, 
                       closed, ver, inboxFreed, held, k, ob, rb, head >>

EX6 == /\ pc[Owner] = "EX6"
       /\ /\ inboxFreed' = (inboxFreed \/ refs = 1)
          /\ refs' = refs - 1
       /\ pc' = [pc EXCEPT ![Owner] = "Done"]
       /\ UNCHANGED << made, freed, carved, used, local, partial, spare, 
                       outstanding, inbox, closed, ver, held, collected, 
                       returned, errs, k, ob, rb, head >>

TheOwner == OW1 \/ OW2 \/ OW2s \/ OW3 \/ EX1 \/ EX2 \/ EX2b \/ EX3 \/ EX4
               \/ EX5 \/ EX6

RR0(self) == /\ pc[self] = "RR0"
             /\ IF ~(held[self] = {} /\ pc[Owner] = "Done")
                   THEN /\ held[self] # {}
                        /\ \E x \in held[self]:
                             /\ held' = [held EXCEPT ![self] = held[self] \ {x}]
                             /\ rb' = [rb EXCEPT ![self] = x]
                        /\ pc' = [pc EXCEPT ![self] = "RR1"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                        /\ UNCHANGED << held, rb >>
             /\ UNCHANGED << made, freed, carved, used, local, partial, spare, 
                             outstanding, inbox, closed, ver, refs, inboxFreed, 
                             collected, returned, errs, k, ob, head >>

RR1(self) == /\ pc[self] = "RR1"
             /\ /\ errs' = (errs \cup Touch(ChunkOf(rb[self])) \cup TouchInbox)
                /\ head' = [head EXCEPT ![self] = [v |-> ver, shut |-> closed]]
             /\ pc' = [pc EXCEPT ![self] = "RR2"]
             /\ UNCHANGED << made, freed, carved, used, local, partial, spare, 
                             outstanding, inbox, closed, ver, refs, inboxFreed, 
                             held, collected, returned, k, ob, rb >>

RR2(self) == /\ pc[self] = "RR2"
             /\ IF head[self].shut
                   THEN /\ pc' = [pc EXCEPT ![self] = "RR4"]
                        /\ UNCHANGED << inbox, ver, errs, head >>
                   ELSE /\ IF ver = head[self].v
                              THEN /\ /\ errs' = (errs \cup TouchInbox)
                                      /\ inbox' = Append(inbox, rb[self])
                                      /\ ver' = ver + 1
                                   /\ IF MutTouchAfter
                                         THEN /\ pc' = [pc EXCEPT ![self] = "RR3"]
                                         ELSE /\ pc' = [pc EXCEPT ![self] = "RR0"]
                                   /\ head' = head
                              ELSE /\ /\ errs' = (errs \cup TouchInbox)
                                      /\ head' = [head EXCEPT ![self] = IF MutStaleHead THEN head[self] ELSE [v |-> ver, shut |-> closed]]
                                   /\ pc' = [pc EXCEPT ![self] = "RR2"]
                                   /\ UNCHANGED << inbox, ver >>
             /\ UNCHANGED << made, freed, carved, used, local, partial, spare, 
                             outstanding, closed, refs, inboxFreed, held, 
                             collected, returned, k, ob, rb >>

RR3(self) == /\ pc[self] = "RR3"
             /\ errs' = (errs \cup Touch(ChunkOf(rb[self])))
             /\ pc' = [pc EXCEPT ![self] = "RR0"]
             /\ UNCHANGED << made, freed, carved, used, local, partial, spare, 
                             outstanding, inbox, closed, ver, refs, inboxFreed, 
                             held, collected, returned, k, ob, rb, head >>

RR4(self) == /\ pc[self] = "RR4"
             /\ /\ errs' = (errs \cup Touch(ChunkOf(rb[self])))
                /\ freed' = (IF outstanding[ChunkOf(rb[self])] = 1 THEN freed \cup {ChunkOf(rb[self])} ELSE freed)
                /\ inboxFreed' = (inboxFreed \/ (outstanding[ChunkOf(rb[self])] = 1 /\ refs - RefDrop = 0))
                /\ outstanding' = [outstanding EXCEPT ![ChunkOf(rb[self])] = outstanding[ChunkOf(rb[self])] - 1]
                /\ refs' = (IF outstanding[ChunkOf(rb[self])] = 1 THEN refs - RefDrop ELSE refs)
                /\ returned' = (returned \cup {rb[self]})
             /\ pc' = [pc EXCEPT ![self] = "RR0"]
             /\ UNCHANGED << made, carved, used, local, partial, spare, inbox, 
                             closed, ver, held, collected, k, ob, rb, head >>

Releaser(self) == RR0(self) \/ RR1(self) \/ RR2(self) \/ RR3(self)
                     \/ RR4(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TheOwner
           \/ (\E self \in Releasers: Releaser(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
