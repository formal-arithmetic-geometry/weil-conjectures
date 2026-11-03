/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedScalarRestrictionTensor
import WeilConjectures.AlgebraicGeometry.ScalarRestrictionConstantPullbackTransport

/-! # Coherence of scalar restriction with constant complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

/-- Scalar restriction commutes with the fixed constant/pullback comparison.
Source: Stacks 0F1E and 0FPI; item proof step 3.
(blueprint: new-lem-pur-scalar-restriction-constant-pullback).
Proof: take the mate of the unique ordinary constant/pullback comparison and
transport it through the exact derived localization factors. The mate identity
for the scalar comparison then gives the displayed formula. -/
theorem scalarRestrictionConstantPullback
    {Z T : Scheme.{u}} (p : Z ⟶ T)
    (H : DerivedCategory (ModuleCat.{u + 1} B)) :
    let U₀ := (ModuleCat.restrictScalars φ).mapDerivedCategory
    let UZ := Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ
    let pA := (upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctor
    let σT := (Functor.mapDerivedCategorySquareIso
      (constantSheafCompSheafComposeIso T.smallEtaleTopology
        (ModuleCat.restrictScalars φ)).symm).hom
    let σZ := (Functor.mapDerivedCategorySquareIso
      (constantSheafCompSheafComposeIso Z.smallEtaleTopology
        (ModuleCat.restrictScalars φ)).symm).hom
    (derivedConstantSheafCompLeftDerivedUpperStarIso
        (ModuleCat.{u + 1} A) p).inv.app (U₀.obj H) ≫
      pA.map (σT.app H) ≫
      (scalarRestrictionPullbackIso φ p).hom.app
        ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)).mapDerivedCategory.obj H) =
    σZ.app H ≫ UZ.map ((derivedConstantSheafCompLeftDerivedUpperStarIso
      (ModuleCat.{u + 1} B) p).inv.app H) := by
  exact scalarRestrictionConstantPullback_transport φ p
    (fun X ↦ scalarRestrictionConstantPullback_underived φ p X) H

end AlgebraicGeometry.Etale
