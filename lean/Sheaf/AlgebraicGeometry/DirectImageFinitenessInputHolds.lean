/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DirectImageFinitenessInput
public import Mathlib.FieldTheory.IsSepClosed
import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
import Sheaf.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility
import Sheaf.AlgebraicGeometry.Sites.CohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.SeparablyClosedTorsionCohomologicalDimension
import Sheaf.AlgebraicGeometry.Sites.FiniteTypeTorsionCohomologicalDimension

/-! # The direct-image finiteness input holds

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-a1-kummer/
`thm-exc-direct-image-input-holds` (blueprint: thm-exc-direct-image-input-holds).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Over a separably closed field and with an integer invertible in the field, the two
clauses of the direct-image finiteness input hold.

Proof:
1. Replace the signed annihilator `N` by its positive absolute value: invertibility
in the field excludes zero, and changing sign preserves invertibility and annihilation.
Use the induced unit in the global sections of `Spec k` to obtain the coefficient
convention required by `thm-dg-finite-type-constructibility`.
Apply `AlgebraicGeometry.Etale.isBoundedConstructible_rightDerivedLowerStar_of_
finiteType_over_field`
to a finite-type morphism and a constructible sheaf in degree zero.  The definition
of bounded constructibility gives constructibility of every higher direct image.
2. For clause (2), let `K` be separably closed and `W` finite type over `K` of
dimension at most `d`. If `W` is empty, all its positive cohomology vanishes.
Otherwise its dimension is a natural number `e` with `e ≤ d`. Apply
`hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed` to `K` and then
`hasTorsionEtaleCohomologicalDimensionLE_of_finiteType` with `c = 0` and exact
dimension `e`, obtaining the bound `2 * e`. Since `2 * e ≤ 2 * d`, the defining
vanishing condition of `HasTorsionEtaleCohomologicalDimensionLE` gives vanishing
for every locally torsion abelian étale sheaf in every degree above `2 * d`.
Source: blueprint `sec-smooth-purity/sk-prop-a1-kummer/`
`thm-exc-direct-image-input-holds.md`
(blueprint: thm-exc-direct-image-input-holds). -/
theorem hasDirectImageFinitenessInput_of_isSepClosed
    (k : Type u) [Field k] [IsSepClosed k] (N : ℤ) (hN : IsUnit (N : k))
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (hΛ : ∀ a : Λ, N • a = 0) :
    HasDirectImageFinitenessInput k N hN Λ hΛ := by
  sorry

end AlgebraicGeometry.Scheme

end
