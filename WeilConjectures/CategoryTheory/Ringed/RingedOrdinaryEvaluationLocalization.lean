/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import all WeilConjectures.SixFunctors.Coefficient.Tensor.CoefficientTensorCurryNormalization
import all WeilConjectures.SixFunctors.SfbHomFilteredColimit.DerivedInternalHomFilteredColimitData
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Limits.HasLimits

/-! # Unsigned ordinary evaluation and its derived localization

Source: Stacks Project, sites-cohomology.tex, Tags 08JD, 08JE, 0A98 and Section 0A8X
(blueprint: lem-sfb-ringed-ordinary-evaluation-localization).

The formulas use the recorded sheafified tensor generators, Hom-product projections,
coefficient-unit identifications, and fixed K-injective augmentation. The ordinary map
exists for arbitrary complexes; only its derived comparison requires the stated K-flatness
and augmentation quasi-isomorphisms.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe c v u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures

namespace CategoryTheory

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

section DerivedDefinitions

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

end DerivedDefinitions

section OrdinaryHelpers

set_option linter.unusedSectionVars false

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

open MonoidalCategory CochainComplex

attribute [local instance 1000001] RingedDerivedNative.cachedCompose
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance 4000] HomologicalComplex.monoidalCategory
attribute [local irreducible] SheafOfModules.monoidalCategory homComplexFunctor
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric
attribute [local instance 1000] RingedDerivedNative.baseLimits RingedDerivedNative.baseColimits
  RingedDerivedNative.gradedTensor RingedDerivedNative.gradedTensorFour
  RingedDerivedNative.gradedTensorLeft RingedDerivedNative.gradedTensorRight
  RingedDerivedNative.baseClosed RingedDerivedNative.auxTensorLeftColimits
  RingedDerivedNative.auxTensorRightColimits
attribute [local instance] SheafOfModules.cochainModulesPreadditive
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

set_option hygiene false in
local notation "Mod" => RingedDerivedNative.Modules.{c, v, u} J R

attribute [local irreducible] ordinaryCurry

attribute [local irreducible] ordinaryAssociator ordinaryRightUnitor
  coefficientTotalTensor coefficientTensorGenerator

attribute [local irreducible] ordinaryEvaluation

attribute [local irreducible] coefficientHomResolution coefficientHomResolutionIso

section DerivedAdjunction

set_option hygiene false in
local notation "Der" => DerivedCategory (RingedTensorModules.{c, v, u} J R)
set_option hygiene false in
local notation "RHom" => derivedInternalHomOfUniverses.{c, v, u, w} J R

variable (S : CoefficientClosedStructure RHom)

end DerivedAdjunction

attribute [local irreducible] HomologicalComplex.quasiIso
  HomologicalComplex.instCategory Preadditive.preadditiveHasZeroMorphisms

attribute [local irreducible] CoefficientClosedStructure.tensor
  CoefficientClosedStructure.transpose ringedOrdinaryHomComparison ringedDualTensorHom
  derivedInternalHomOfUniverses CoefficientTensorModels.iso ringedTensorUnitComplex

end OrdinaryHelpers

variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, u} J R)]

end CategoryTheory
