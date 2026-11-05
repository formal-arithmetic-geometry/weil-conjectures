/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import all WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Localization.Construction
import all Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import all Mathlib.CategoryTheory.Functor.Currying
import all Mathlib.CategoryTheory.Whiskering
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Localization.Prod
import all Mathlib.Algebra.Homology.BifunctorFlip
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all Mathlib.CategoryTheory.Localization.CalculusOfFractions
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import all WeilConjectures.CategoryTheory.Principal.PrincipalKoszulQuotientTowersSupplement
import all WeilConjectures.Algebra.Homology.FlatSingleTensor.RingedFlatSingleTensorCohomology
import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictSectionQuotientConeMaps
import all WeilConjectures.Algebra.Homology.KFlatRoos.KFlatRoosRepresentativeInvariance
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Mathlib.CategoryTheory.Localization.Predicate
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Normalized tensor models for section principal quotients -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures
open scoped CategoryTheory.Obj TensorProduct
open CategoryTheory.InternalAbelianSheafModule

-- Upstream's `HasDerivedCategory` instances on these module categories are found first and then
-- fail the final defeq check, which blocks `HasDerivedCategory.ofIsGrothendieckAbelian`.
attribute [-instance] AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory
  AlgebraicGeometry.Scheme.ProjectionRestriction.derived
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOver
  AlgebraicGeometry.Scheme.ProjectionRestriction.derivedOverModules

open AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction

attribute [local irreducible] derivedInternalHomOfUniverses CoefficientClosedStructure.tensor
  SheafOfModules.monoidalCategory
attribute [local irreducible] coefficientTotalTensor CoefficientTensorModels.iso
section TensorLocalization
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (R : Sheaf J CommRingCat.{u + 1})

variable [HasDerivedCategory.{u + 1} (SheafOfModules.{u + 1} ((sheafCompose J
  (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R))]

variable (H : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} J R))
  (HM : CoefficientTensorModels.{u, u + 1, u, u + 1} J R H)

attribute [local semireducible] coefficientTotalTensor

end TensorLocalization

section Singleton
attribute [local semireducible] coefficientTotalTensor
attribute [local irreducible] CochainComplex.mapBifunctorSingle₂Iso
  SheafOfModules.siteSheafTensorRightIso
variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{u + 1}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  (R : Sheaf J CommRingCat.{u + 1})
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
open MonoidalCategory

@[irreducible] private def singleComparisonNatural (N : GS J R) :
    Prod.sectL (GC J R) ((HomologicalComplex.single _ (.up ℤ) 0).obj N) ⋙ GT J R ≅
      (SheafOfModules.siteSheafTensorRight N).mapHomologicalComplex (.up ℤ) :=
  uncurry_flip_iso
    ((curriedTensor (GS J R)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))
      ((HomologicalComplex.single _ (.up ℤ) 0).obj N) ≪≫
    CochainComplex.map₂HomologicalComplexFlipObjSingleIso (curriedTensor (GS J R)) N ≪≫
    NatIso.mapHomologicalComplex (SheafOfModules.siteSheafTensorRightIso R N).symm (.up ℤ)

@[irreducible] private def singleComparison (N : GS J R) (P : GC J R) :
    (GT J R).obj (P, (HomologicalComplex.single _ (.up ℤ) 0).obj N) ≅
      ((SheafOfModules.siteSheafTensorRight N).mapHomologicalComplex (.up ℤ)).obj P :=
  (singleComparisonNatural J R N).app P

attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification

end Singleton

section Assembly
attribute [local irreducible] SheafOfModules.KFlatRoos.algebraModule
attribute [local implicit_reducible] HomologicalComplex.asFunctor CochainComplex.singleFunctors
  Prod.sectL
attribute [local irreducible] CochainComplex.mapBifunctorSingle₂Iso
  SheafOfModules.siteSheafTensorRightIso PresheafOfModules.sheafificationAdjunction
  SheafOfModules.tensorObjIsoSheafification
attribute [local irreducible] SheafOfModules.KFlatRoos.tensorUnit
  SheafOfModules.siteSheafTensorRight SheafOfModules.KFlatRoos.roos
  SheafOfModules.siteSheafTensorTmul coefficientTensorGenerator
variable (X : Scheme.{u})
  (R : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
  (H : CoefficientClosedStructure
    (derivedInternalHomOfUniverses.{u + 1, u, u, u + 1} (Scheme.ProEt.topology X) R))
  (HM : CoefficientTensorModels.{u, u + 1, u, u + 1} (Scheme.ProEt.topology X) R H)
  (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
  (ι : (Functor.const ℕᵒᵖ).obj R ⟶ B)

end Assembly

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction
