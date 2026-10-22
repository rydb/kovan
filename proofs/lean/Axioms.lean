import Kovan
import Lean

/-!
# The axioms the proofs rest on

Lean checks every step of a proof, but a proof may also lean on an axiom: a fact taken without
proof. Lean's own three are `propext` (two propositions that imply each other are equal),
`Quot.sound` (two values a quotient identifies are equal) and `Classical.choice` (from a proof
that something exists, pick one). A proof with a hole in it rests on `sorryAx`, and a proof that
ran compiled code rests on `Lean.ofReduceBool`.

`check.sh axioms` compiles this file. The command below walks every theorem whose name starts with
`Kovan`, collects the axioms each one rests on through every lemma it uses, and fails naming the
theorem if any of them is not one of Lean's three. It walks the library itself, so a new theorem is
checked the day it is written: nothing here lists theorems by hand.

This file is not part of the library, so `lake build` does not run it.
-/

open Lean Elab Command

/-- `#assert_standard_axioms Root` fails unless every theorem under `Root` rests only on
`propext`, `Quot.sound` and `Classical.choice`. On success it says how many theorems it checked,
and it fails if there are none, so a misspelt root cannot pass by checking nothing. -/
elab "#assert_standard_axioms " root:ident : command => do
  let root := root.getId
  let standard : List Name := [``propext, ``Quot.sound, ``Classical.choice]
  let env ← getEnv
  let mut checked : Nat := 0
  let mut offending : Array MessageData := #[]
  for (name, info) in env.constants.toList do
    -- Only the library's own theorems: definitions carry no proof, and the names Lean makes up
    -- for the pieces of a proof are covered through the theorem that uses them.
    unless root.isPrefixOf name && !name.isInternal do continue
    let .thmInfo _ := info | continue
    checked := checked + 1
    for ax in ← collectAxioms name do
      unless standard.contains ax do
        offending := offending.push m!"{name} rests on {ax}"
  if checked == 0 then
    throwError "no theorem is named under {root}: check the name given to #assert_standard_axioms"
  unless offending.isEmpty do
    throwError "these theorems rest on an axiom that is not one of Lean's three:\n{MessageData.joinSep offending.toList "\n"}"
  logInfo m!"all {checked} theorems under {root} rest only on propext, Quot.sound and Classical.choice"

#assert_standard_axioms Kovan
