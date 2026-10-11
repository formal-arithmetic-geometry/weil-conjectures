/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionComparison
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.Shift

/-!
# The adjunctions of the derived six functors commute with shifts

The functors `Lg^*`, `Rg_*`, `Rf_!`, `Rf^!` and `K ⊗ᴸ -` on the unbounded derived categories of
étale sheaves commute with the shift functors (`WeilConjectures.SixFunctors.Etale.Derived.Shift`).
This file equips the derived hom `RHom(K, -)` with its `CommShift` structure, as the right
adjoint of `K ⊗ᴸ -`, and shows that the three adjunctions `Lg^* ⊣ Rg_*`, `Rf_! ⊣ Rf^!` and
`K ⊗ᴸ - ⊣ RHom(K, -)` are compatible with these structures
(`CategoryTheory.Adjunction.CommShift`): their units and counits commute with the shifts.

For `Lg^* ⊣ Rg_*` this is not formal: the shift structure of `Rg_*` comes from the adjunction
`D(g^*) ⊣ Rg_*` with the levelwise pullback, and that of `Lg^*` from the isomorphism
`Lg^* ≅ D(g^*)`. The derived adjunction `Lg^* ⊣ Rg_*` is the levelwise one transported along
this isomorphism (`CategoryTheory.Adjunction.derivedAdjunction_eq_ofNatIsoLeft`).

## Main definitions and results

- `AlgebraicGeometry.Etale.commShiftDerivedHomObj`: `RHom(K, -)` commutes with shifts.
- `AlgebraicGeometry.Etale.commShift_derivedTensorHomAdjunction`,
  `AlgebraicGeometry.Etale.commShift_derivedUpperStarLowerStarAdjunction`,
  `AlgebraicGeometry.Etale.commShift_rightDerivedUpperShriekAdjunction`: the adjunctions
  `K ⊗ᴸ - ⊣ RHom(K, -)`, `Lg^* ⊣ Rg_*` and `Rf_! ⊣ Rf^!` commute with shifts.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

/-- The adjunction `Rf_! ⊣ Rf^!` commutes with shifts: the shift structure of `Rf^!` is the
one induced by the adjunction. -/
instance commShift_rightDerivedUpperShriekAdjunction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] [(R(f)_![A]).IsLeftAdjoint] :
    (rightDerivedUpperShriekAdjunction A f).CommShift ℤ :=
  (rightDerivedUpperShriekAdjunction A f).commShift_of_leftAdjoint ℤ

variable [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The adjunction `Lg^* ⊣ Rg_*` commutes with shifts. It is the adjunction `D(g^*) ⊣ Rg_*`,
which defines the shift structure of `Rg_*`, transported along the isomorphism
`Lg^* ≅ D(g^*)` which defines the shift structure of `Lg^*`. -/
instance commShift_derivedUpperStarLowerStarAdjunction {Z Y : Scheme.{u}} (g : Z ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction A g).CommShift ℤ := by
  have : (mapDerivedUpperStarLowerStarAdjunction A g).CommShift ℤ :=
    (mapDerivedUpperStarLowerStarAdjunction A g).commShift_of_leftAdjoint ℤ
  have : NatTrans.CommShift (leftDerivedUpperStarIsoMapDerivedCategory A g).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (leftDerivedUpperStarIsoMapDerivedCategory A g).symm ℤ
  rw [derivedUpperStarLowerStarAdjunction, Adjunction.derivedAdjunction_eq_ofNatIsoLeft]
  exact Adjunction.CommShift.ofNatIsoLeft (mapDerivedUpperStarLowerStarAdjunction A g)
    (leftDerivedUpperStarIsoMapDerivedCategory A g).symm

variable {X : Scheme.{u}}

/-- The derived hom `RHom(K, -)` commutes with shifts, being right adjoint to `K ⊗ᴸ -`. -/
noncomputable instance commShiftDerivedHomObj
    (K : (DerivedCategory (Sheaf X.smallEtaleTopology A))ᵒᵖ) :
    ((RHom(X)[A]).obj K).CommShift ℤ :=
  (derivedTensorHomAdjunction A K.unop).rightAdjointCommShift ℤ

/-- The adjunction `K ⊗ᴸ - ⊣ RHom(K, -)` commutes with shifts. -/
instance commShift_derivedTensorHomAdjunction
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedTensorHomAdjunction A K).CommShift ℤ :=
  (derivedTensorHomAdjunction A K).commShift_of_leftAdjoint ℤ

end Etale

end AlgebraicGeometry
