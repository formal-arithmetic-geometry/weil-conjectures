/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Init
public meta import Lean.Elab.Tactic.ElabTerm

/-!
# The tactic `exact_mod_proofs`

`exact_mod_proofs h` closes the goal `G` using a term `h : H` when, at every position where `H`
and `G` differ, both subterms are closed proofs (e.g. different elaborations of the same instance
of a `Prop`-valued class, some of them auxiliary proof constants), or closed definitionally equal
terms (e.g. two paths to the same data-carrying instance), which are left to the kernel. Unlike
`exact_mod_proof_irrel`, any number of distinct proofs may occur.

The proofs are definitionally equal by proof irrelevance, but when they occur deep inside the
implicit arguments of large types, checking this definitional equality can make the unifier and
the kernel unfold the surrounding definitions. The tactic instead chooses a representative `r` in
each class of proofs identified by the differences, and casts both `h` and the goal along the
motives `fun z⃗ ↦ H[c⃗ := z⃗]` and `fun z⃗ ↦ G[c⃗ := z⃗]` (all the other proofs `c` replaced
simultaneously) and the equations `c = r` (closed by `rfl`, checked by proof irrelevance on the
proofs alone). The two casted types differ only at the definitionally equal non-proof terms, if
any.

The variant `cast_proofs h` casts the goal along `proof_irrel` one pair of differing proofs at a
time, at exactly the positions where they differ. Its motives stay close to the goal itself, so
the kernel check stays cheap even with thousands of differing positions, where the single
simultaneous cast of `exact_mod_proofs` can exhaust the kernel.
-/

public meta section

namespace ExactModProofs

open Lean Meta Elab Tactic

/-- `exact_mod_proofs h` closes the goal with `h` when the type of `h` and the goal differ only
by closed proofs, at any number of positions, and by closed definitionally equal terms. -/
elab "exact_mod_proofs " h:term : tactic => withMainContext do
  exactModProofs (← elabTerm h none)

/-- `cast_proofs h` closes the goal with `h` when the type of `h` and the goal differ only by
closed proofs, at any number of positions, and by closed definitionally equal terms. Unlike
`exact_mod_proofs`, the goal is cast along one pair of differing proofs at a time, which keeps
the motives small for the kernel. -/
elab "cast_proofs " h:term : tactic => withMainContext do
  castProofs (← elabTerm h none)

end ExactModProofs
