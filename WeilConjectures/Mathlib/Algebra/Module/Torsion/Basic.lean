/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Submodules annihilated by an ideal

A submodule `N` of an `R`-module `M` is a torsion module for an ideal `J` of `R` exactly when
`J • N = ⊥`. Through `Module.IsTorsionBySet.module` this makes `N` a module over `R ⧸ J`.

## Main results

* `Module.isTorsionBySet_iff_smul_eq_bot`: a submodule is `J`-torsion if and only if it is
  annihilated by `J`.
-/

@[expose] public section

/-- **A submodule is `J`-torsion if and only if `J` annihilates it.** Through
`Module.IsTorsionBySet.module` the forward direction makes `N` a module over `R ⧸ J`. For `N`
an ideal of `R` the right-hand side is `J * N = ⊥`, by `Ideal.smul_eq_mul`. -/
theorem Module.isTorsionBySet_iff_smul_eq_bot {R M : Type*} [CommSemiring R] [AddCommMonoid M]
    [Module R M] {J : Ideal R} {N : Submodule R M} :
    Module.IsTorsionBySet R N (J : Set R) ↔ J • N = ⊥ :=
  (Module.isTorsionBySet_iff_subset_annihilator R N).trans
    (SetLike.coe_subset_coe.trans Submodule.le_annihilator_iff)
