/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates

import WeilConjectures.Algebra.Homology.DerivedTensorFirstLocalizationModels
import WeilConjectures.Algebra.Homology.AffineStalkScalarExtensionCoordinates
import WeilConjectures.Algebra.Homology.BaseDerivedTensorModelQuasiIsoComparison
import WeilConjectures.Algebra.Homology.AffineStalkBaseSecondLocalizationComparison

/-! Core derived localization and stalk comparison glue.
(blueprint: new-affine-direct-localized-tensor-square-core). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
noncomputable section
namespace AlgebraicGeometry

/-- Keep the tensor-algebra coefficient map abstract; its restrictions are the API. -/
@[irreducible] private def tensorCoefficientMap
    (R Aq B D : Type u) [CommRing R] [CommRing Aq] [CommRing B] [CommRing D]
    [Algebra R Aq] [Algebra R B] [Algebra R D]
    (a : Aq →ₐ[R] D) (b : B →ₐ[R] D) : Aq ⊗[R] B →+* D :=
  (Algebra.TensorProduct.lift (R := R) (S := R) a b
    (fun _ _ ↦ Commute.all _ _)).toRingHom

/-- Scalar composition in each degree, with naturality for the differentials. -/
@[irreducible] private noncomputable def coefficientExtensionIso
    (A Aq D : Type u) [CommRing A] [CommRing Aq] [CommRing D]
    (rho : A →+* Aq) (f0 : A →+* D) (f1 : Aq →+* D) (h : f1.comp rho = f0)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendScalars f0).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((ModuleCat.extendScalars f1).mapHomologicalComplex (.up ℤ)).obj
        (((ModuleCat.extendScalars rho).mapHomologicalComplex (.up ℤ)).obj M) := by
  subst f0
  exact HomologicalComplex.Hom.isoOfComponents
    (fun j ↦ (ModuleCat.extendScalarsComp rho f1).app (M.X j))
    (fun j k _ ↦ ((ModuleCat.extendScalarsComp rho f1).hom.naturality (M.d j k)).symm)

/-- Equal scalar maps, kept abstract to avoid repeated whole-complex equality casts. -/
@[irreducible] private noncomputable def scalarComplexIso
    (A D : Type u) [CommRing A] [CommRing D] (f g : A →+* D) (h : f = g)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).obj M :=
  eqToIso (congrArg
    (fun φ : A →+* D ↦ ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M) h)

/-- Keep the universal model constructor abstract during comparison elaboration. -/
@[irreducible] private noncomputable def affineTensorModel
    (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} B)]
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) :
    ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D :=
  ModuleCat.baseDerivedTensorCohomologyModel R A B Q D

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

end AlgebraicGeometry
