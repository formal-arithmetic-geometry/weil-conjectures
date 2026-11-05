/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `exact_mod_proof_irrel`

`exact_mod_proof_irrel h` closes the goal `G` using a hypothesis `h : H` when `H` and `G` differ
only by two proofs `c₁ c₂ : P` of the same proposition, occurring at different positions in `H`
and `G` (e.g. two elaborations of the same instance of a `Prop`-valued class, one of them an
auxiliary proof constant). Such terms are definitionally equal by proof irrelevance, but when they
occur deep inside the implicit arguments of large types, checking this definitional equality can
make the kernel unfold the surrounding definitions. The tactic instead abstracts `c₁` and `c₂` to
variables `x y : P` and transports `h` along the equation `x = y` with `Eq.rec`, so that the kernel
only has to compare syntactically equal terms.
-/

public meta section

namespace ExactModProofIrrel

open Lean Meta Elab Tactic

/-- `exact_mod_proof_irrel h` closes the goal with `h` when the type of `h` and the goal differ
only by two proofs of the same proposition, possibly at several positions. -/
elab "exact_mod_proof_irrel " h:term : tactic => withMainContext do
  exactModProofIrrel (← elabTerm h none)

end ExactModProofIrrel
