/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `transport_mod_proofs`

`transport_mod_proofs h` closes the goal `G` using a term `h : H` when `H` and `G` differ only
by closed proofs (e.g. different elaborations of the same instance of a `Prop`-valued class, some
of them auxiliary proof constants), at any number of positions, and possibly with several
different proofs of the same proposition occurring both in `H` and in `G`.

It proceeds one difference at a time: at the first position where `H` and `G` differ, with proofs
`a` in `H` and `b` in `G`, it replaces every occurrence of `b` by `a`, both in `H` and in `G`,
casting `h` and the goal along `congrArg (fun x ↦ H[b := x]) (proof_irrel b a)` and its analogue
for `G`. Each cast only asks the kernel to compare syntactically equal terms and the types of the
two proofs `a` and `b`. Unlike `exact_mod_proofs`, which casts along a single motive abstracting
all the differing proofs at once and so asks the kernel to compare the types of the chosen
representatives with those of all other proofs of their class, this does not make the kernel
unfold the large types in which the proofs occur.
-/

public meta section

namespace TransportModProofs

open Lean Meta Elab Tactic

/-- `transport_mod_proofs h` closes the goal with `h` when the type of `h` and the goal differ
only by closed proofs, at any number of positions. -/
elab "transport_mod_proofs " h:term : tactic => withMainContext do
  transportModProofs (← elabTerm h none)

end TransportModProofs
