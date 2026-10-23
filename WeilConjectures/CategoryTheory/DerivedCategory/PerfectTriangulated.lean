/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect

/-!

# The triangulated subcategory `Perf(R)` of `D(R)`

For a commutative ring `R`, `Perf(R) ⊂ D(R)` consists of the objects represented by bounded
complexes of finitely generated projective `R`-modules (`DerivedCategory.IsPerfect`). This file
records it as an object property of `D(R)` and shows that it is a triangulated subcategory,
closed under isomorphisms.

## Main definitions

- `DerivedCategory.perfect`: the object property `Perf(R)` of `D(R)`.

## Main statements

- `DerivedCategory.isTriangulated_perfect`: `Perf(R)` is a triangulated subcategory of `D(R)`.

-/

@[expose] public section

universe u

open CategoryTheory Limits ZeroObject

namespace DerivedCategory

variable (R : Type u) [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]

/-- Blueprint `sk-d-setup`: the subcategory `Perf(R) ⊂ D(R)` of objects represented by bounded
complexes of finitely generated projective `R`-modules. -/
def perfect : ObjectProperty (DerivedCategory (ModuleCat.{u} R)) :=
  fun C ↦ C.IsPerfect

instance : (perfect R).IsClosedUnderIsomorphisms where
  of_iso e h := IsPerfect.of_iso h e

/-- `Perf(R)` is a triangulated subcategory of `D(R)`. -/
instance isTriangulated_perfect : (perfect R).IsTriangulated where
  exists_zero := by
    have hX (i : ℤ) : IsZero ((0 : CochainComplex (ModuleCat.{u} R) ℤ).X i) :=
      (HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _)
    have : (0 : CochainComplex (ModuleCat.{u} R) ℤ).IsStrictlyGE 0 :=
      (CochainComplex.isStrictlyGE_iff _ _).2 fun i _ ↦ hX i
    have : (0 : CochainComplex (ModuleCat.{u} R) ℤ).IsStrictlyLE 0 :=
      (CochainComplex.isStrictlyLE_iff _ _).2 fun i _ ↦ hX i
    refine ⟨_, Q.map_isZero (isZero_zero _), isPerfect_Q_obj _ 0 0 fun i ↦ ?_⟩
    let e := (hX i).iso (ModuleCat.isZero_of_subsingleton (ModuleCat.of R PUnit))
    exact ⟨Module.Projective.of_equiv e.toLinearEquiv.symm,
      Module.Finite.equiv e.toLinearEquiv.symm⟩
  isStableUnderShiftBy n := ⟨fun _ h ↦ IsPerfect.shift h n⟩
  ext₂' T hT h₁ h₃ := ObjectProperty.le_isoClosure _ _ (isPerfect_obj₂_of_distTriang T hT h₁ h₃)

end DerivedCategory
