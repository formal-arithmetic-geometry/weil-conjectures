/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# The `I`-depth of a module

For an ideal `I` of a commutative ring `R` and an `R`-module `M`, the `I`-depth of `M` is the
supremum of the lengths of `M`-regular sequences in `I` if `I • M ≠ M`, and `∞` otherwise
(Stacks, Algebra, Definition 00LF).

## Main definitions

- `Ideal.depth`: the `I`-depth of a module, valued in `ℕ∞`.
- `IsLocalRing.depth`: the depth of a module over a local ring.
-/

@[expose] public section

namespace Ideal

variable {R : Type*} [CommRing R]

/-- The `I`-depth of an `R`-module `M`: if `I • M ≠ M` it is the supremum (in `ℕ∞`) of the
lengths of the `M`-regular sequences all of whose members lie in `I`; if `I • M = M` it is `∞`.
(blueprint: `def-weil-pbc-depth`) -/
noncomputable def depth (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  open Classical in
  if I • (⊤ : Submodule R M) = ⊤ then ⊤ else
    ⨆ (rs : List R) (_ : ∀ r ∈ rs, r ∈ I) (_ : RingTheory.Sequence.IsRegular M rs),
      (rs.length : ℕ∞)

lemma depth_eq_top_of_smul_eq_top (I : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]
    (h : I • (⊤ : Submodule R M) = ⊤) : I.depth M = ⊤ := by
  simp [depth, h]

end Ideal

namespace IsLocalRing

variable (R : Type*) [CommRing R] [IsLocalRing R]

/-- The depth of a module over a local ring: the `𝔪`-depth for the maximal ideal `𝔪`.
(blueprint: `def-weil-pbc-depth`) -/
noncomputable abbrev depth (M : Type*) [AddCommGroup M] [Module R M] : ℕ∞ :=
  (maximalIdeal R).depth M

end IsLocalRing
