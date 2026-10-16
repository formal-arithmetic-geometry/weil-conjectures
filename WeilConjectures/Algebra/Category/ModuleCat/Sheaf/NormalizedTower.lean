/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange

/-!
# Normalized adic towers of sheaves of modules

Let `(C, J)` be an essentially small site, `R` a commutative ring and `I` an ideal of `R`, and
put `P_n = R ⧸ Iⁿ`. A *normalized tower* (an adic tower in the sense of blueprint
`def-weil-pbc-adic-coefficient-datum`) is a family of objects `M_n ∈ D(J, P_n)` with transition
maps `M_{n+1} ⟶ Res M_n` exhibiting `M_n` as the derived base change
`M_{n+1} ⊗ᴸ_{P_{n+1}} P_n` (`CategoryTheory.Sheaf.IsDerivedBaseChange`): these are the
normalization isomorphisms `M_{n+1} ⊗ᴸ_{P_{n+1}} P_n ≅ M_n`, and the transition maps between
arbitrary levels, the composites of the consecutive ones, satisfy the quotient cocycle.

The level `n = 0` is the zero ring `R ⧸ I⁰`, so that the indexing agrees with the tower of
reductions `n ↦ K ⊗ᴸ R/Iⁿ` of `DerivedCategory.derivedCompletionDiagram` and with the normalized
adic towers of complexes `CochainComplex.IsNormalizedAdicTower`.

This is the version on an arbitrary site of `AlgebraicGeometry.Etale.NormalizedTower` (which is
indexed by `n ↦ R ⧸ Iⁿ⁺¹` on the small étale site).

## Main definitions

- `CategoryTheory.Sheaf.NormalizedTower J I`: normalized towers.
- `CategoryTheory.Sheaf.NormalizedTower.restrict`: the underlying tower `n ↦ Res M_n` in
  `D(J, R)`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C) {R : Type (u + 1)} [CommRing R] (I : Ideal R)

/-- A *normalized tower* of sheaves of modules: objects `M_n ∈ D(J, R ⧸ Iⁿ)` with transition
maps `M_{n+1} ⟶ Res M_n` exhibiting `M_n` as the derived base change
`M_{n+1} ⊗ᴸ_{R ⧸ Iⁿ⁺¹} R ⧸ Iⁿ` (the normalization isomorphisms of an adic tower, blueprint
`def-weil-pbc-adic-coefficient-datum`). -/
structure NormalizedTower where
  /-- The level `M_n ∈ D(J, R ⧸ Iⁿ)`. -/
  obj (n : ℕ) : DerivedCategory (Sheaf J (ModuleCat.{u + 1} (R ⧸ I ^ n)))
  /-- The transition map `M_{n+1} ⟶ Res M_n`. -/
  map (n : ℕ) : obj (n + 1) ⟶
    (derivedRestrictScalars J (Ideal.Quotient.factorPowSucc I n)).obj (obj n)
  /-- The transition maps are normalization maps: `M_{n+1} ⊗ᴸ R ⧸ Iⁿ ≅ M_n`. -/
  isDerivedBaseChange (n : ℕ) : IsDerivedBaseChange (map n)

namespace NormalizedTower

variable {J I} (M : NormalizedTower J I)

/-- The underlying tower `n ↦ Res M_n` of a normalized tower in `D(J, R)`, with the
restrictions of scalars of the transition maps. -/
noncomputable def restrict : ℕᵒᵖ ⥤ DerivedCategory (Sheaf J (ModuleCat.{u + 1} R)) :=
  Functor.ofOpSequence (X := fun n ↦
    (derivedRestrictScalars J (Ideal.Quotient.mk (I ^ n))).obj (M.obj n)) fun n ↦
    (derivedRestrictScalars J (Ideal.Quotient.mk (I ^ (n + 1)))).map (M.map n) ≫
      (derivedRestrictScalarsCompIso J
        (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right n.le_succ)).symm).hom.app
        (M.obj n)

@[simp]
lemma restrict_obj (n : ℕ) :
    M.restrict.obj (op n) =
      (derivedRestrictScalars J (Ideal.Quotient.mk (I ^ n))).obj (M.obj n) :=
  rfl

lemma restrict_map_succ (n : ℕ) :
    M.restrict.map (homOfLE n.le_succ).op =
      (derivedRestrictScalars J (Ideal.Quotient.mk (I ^ (n + 1)))).map (M.map n) ≫
        (derivedRestrictScalarsCompIso J
          (Ideal.Quotient.factor_comp_mk (Ideal.pow_le_pow_right n.le_succ)).symm).hom.app
          (M.obj n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

end NormalizedTower

end CategoryTheory.Sheaf
