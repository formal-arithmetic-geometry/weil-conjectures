/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.ReductionLowerShriekShift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionHom
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
import Mathlib.CategoryTheory.Sites.Point.IsMonoidalW

/-!
# The tensor comparison of the derived extension of scalars commutes with shifts

Let `Ψ = - ⊗ᴸ_Λ Λ'` be the derived extension of scalars along a surjective ring morphism with
principal kernel (`AlgebraicGeometry.Etale.derivedExtendScalars`), with the commutation with the
shifts induced, as a left adjoint, by the one of the restriction of scalars. Its counit
`Qh ⋙ Ψ ⟶ K(Λ' ⊗_Λ -) ⋙ Qh` commutes with the shifts
(`AlgebraicGeometry.Etale.commShift_derivedExtendScalarsCounit`), hence so does its tensor
comparison `Ψ(K ⊗ᴸ M) ⟶ Ψ K ⊗ᴸ Ψ M` in each variable
(`AlgebraicGeometry.Etale.derivedExtendScalars_tensorComparison_shift_left`,
`AlgebraicGeometry.Etale.derivedExtendScalars_tensorComparison_shift_right`).
-/

@[expose] public section

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly, as in the definition of
-- the derived tensor product.
attribute [-instance]
  CategoryTheory.instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

universe u

open CategoryTheory Limits MonoidalCategory

-- the instances used in the definition of the derived tensor product of étale sheaves
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a}) (X : Scheme.{u})

/-- The counit `Qh ⋙ Ψ ⟶ K(Λ' ⊗_Λ -) ⋙ Qh` of the derived extension of scalars commutes with the
shifts. -/
instance commShift_derivedExtendScalarsCounit :
    NatTrans.CommShift (derivedExtendScalarsCounit hρ ha X) ℤ :=
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  (Sheaf.extendScalarsAdjunction X.smallEtaleTopology
    ρ).commShift_leftDerivedFunctorCounit_of_adjunction

/-- The tensor comparison `Ψ(K ⊗ᴸ -) ⟶ Ψ K ⊗ᴸ Ψ(-)` of the derived extension of scalars, for a
fixed `K`. -/
noncomputable abbrev derivedExtendScalarsTensorComparisonApp
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedTensor (ModuleCat.{u + 1} Λ) X).obj K ⋙ derivedExtendScalars hρ ha X ⟶
      derivedExtendScalars hρ ha X ⋙
        (derivedTensor (ModuleCat.{u + 1} Λ') X).obj ((derivedExtendScalars hρ ha X).obj K) :=
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  let τ := (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedTensorComparisonApp K
  τ

/-- The tensor comparison `Ψ(- ⊗ᴸ M) ⟶ Ψ(-) ⊗ᴸ Ψ M` of the derived extension of scalars, for a
fixed `M`. -/
noncomputable abbrev derivedExtendScalarsTensorComparisonFlipApp
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj M ⋙ derivedExtendScalars hρ ha X ⟶
      derivedExtendScalars hρ ha X ⋙
        (derivedTensor (ModuleCat.{u + 1} Λ') X).flip.obj ((derivedExtendScalars hρ ha X).obj M) :=
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedTensorComparisonFlipApp M

-- test a
set_option maxHeartbeats 40000 in
example : derivedTensor (ModuleCat.{u + 1} Λ') X =
    Functor.testTargetTensor
      (D := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) := rfl

-- test b
set_option maxHeartbeats 40000 in
example : derivedTensor (ModuleCat.{u + 1} Λ) X =
    Functor.testSourceTensor (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) := rfl
end AlgebraicGeometry.Etale
