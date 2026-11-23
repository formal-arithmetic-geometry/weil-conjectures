/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-! # Derived scalar extension for fixed-coefficient module sheaves

Source: Stacks Project, Tags 06YY and 06XN.

The general ringed-site and ordinary-module universal pairs are retained
(`nonempty_derivedChangeOfRingsCochainModel` records both K-flat invariance and the full
universal derived pair). This file gives their fixed-coefficient sheaf specialization, as the
left adjoint to the existing exact derived restriction of scalars.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

variable {C : Type (u + 1)} [Category.{u} C] [EssentiallySmall.{u + 1} C]
  (J : GrothendieckTopology C)

/-- Derived restriction has a left adjoint for every map of constant coefficient rings.
Source: Stacks 06YY, 06XN. -/
theorem fixedCoefficientDerivedRestriction_isRightAdjoint
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    (derivedRestrictScalars J φ).IsRightAdjoint := by
  let := φ.toAlgebra
  have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} A)) :=
    ⟨fun _ _ ↦ (inferInstance : HasColimitsOfSize.{0, 0}
      (Sheaf J (ModuleCat.{u + 1} A))).has_colimits_of_shape _⟩
  have : (extendScalars J φ).PreservesKFlatQuasiIso := by
    constructor
    intro P Q hP hQ f hf
    exact CochainComplex.quasiIso_map_of_iso_tensorRight _ _
      (extendScalarsCompRestrictScalarsIso J A B) f hP hQ
  exact ((extendScalarsAdjunction J φ).derivedAdjunction.ofNatIsoRight
    (restrictScalars J φ).rightDerivedFunctorIsoMapDerivedCategory).isRightAdjoint

/-- Canonical derived extension of scalars, determined up to its unique
adjunction-compatible isomorphism by the existing derived restriction functor.
The preceding theorem constructs it by sheafified tensor and K-flat resolutions;
no arbitrary map or independent scalar action is selected.
Source: Stacks 06YY. -/
noncomputable def fixedCoefficientDerivedScalarExtension
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) :
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u + 1} B)) :=
  letI := fixedCoefficientDerivedRestriction_isRightAdjoint J φ
  (derivedRestrictScalars J φ).leftAdjoint

end CategoryTheory.Sheaf
