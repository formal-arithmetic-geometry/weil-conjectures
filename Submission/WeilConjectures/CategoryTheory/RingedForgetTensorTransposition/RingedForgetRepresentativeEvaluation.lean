/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorDescent
import all Submission.WeilConjectures.CategoryTheory.Ringed.Slice.RingedSliceRepresentativeEvaluation
import all Submission.WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all Submission.WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all Submission.WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all Submission.WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Submission.WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all Submission.WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Submission.WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all Submission.WeilConjectures.CategoryTheory.RingedToposRingData
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all Submission.WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Submission.WeilConjectures.Algebra.Homology.InternalHom
import all Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
import all Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all Submission.WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import Submission.WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetChainUncurry
import Submission.WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetHomRepresentative

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Evaluation compatibility on K-flat and K-injective representatives

Source: Stacks 08J9, 070I; steps 5--8 of ringed tensor transposition
(blueprint: lem-sf-ringed-forget-representative-evaluation).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe b vb a va c v r d vd s wb wa

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures

namespace CategoryTheory.RingedForgetTensorTransposition

-- Reuse the small-site transport directly when elaborating coefficient-ring compositions.
attribute [local instance 1000001] RingedDerivedNative.cachedCompose
attribute [local instance 20000] siteAbelianHasSheafify siteAbelianWEqualsLocallyBijective

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

variable (χ : RingedForgetTwoInjective.Comparison.{wb, wa, c, v, r, d, vd, s}
    J R J' R' U u.hom)

attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolution coefficientHomResolutionIso coefficientHomResolutionInverse
  coefficientTotalTensor coefficientTensorGenerator CoefficientTensorModels.iso

private def makeComparisonData
    {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
    (HB : Bᵒᵖ × B ⥤ B) (HA : Aᵒᵖ × A ⥤ A) (F : B ⥤ A)
    (S : CoefficientClosedStructure HB) (T : CoefficientClosedStructure HA)
    (β : @SymmetricCategory B _ S.monoidal)
    (γ : @SymmetricCategory A _ T.monoidal)
    (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)
    (η : HB ⋙ F ≅ (F.op.prod F) ⋙ HA) :
    RingedSliceEvaluationComparisons HB HA F S T True where
  rho M K := μ.app (M, K)
  eta K L := η.app (op K, L)
  rho_naturality M K M' K' f g :=
    μ.hom.naturality (X := (M, K)) (Y := (M', K')) (f, g)
  eta_naturality K L K' L' f g :=
    η.hom.naturality (X := (op K, L)) (Y := (op K', L')) (f.op, g)
  sigma M K := β.toBraidedCategory.braiding M K
  sigma_naturality M K M' K' f g := by
    let := S.monoidal
    let := β
    exact BraidedCategory.braiding_naturality f g
  sigmaU M K := γ.toBraidedCategory.braiding M K
  sigmaU_naturality M K M' K' f g := by
    let := T.monoidal
    let := γ
    exact BraidedCategory.braiding_naturality f g
  kflat := True.intro

private def comparisonData
    (m : TensorComparison.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U u SB TB βB cB SA TA βA cA) :
    RingedSliceEvaluationComparisons
      (derivedInternalHomOfUniverses.{c, v, r, wb} J R)
      (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R')
      U.mapDerivedCategory SB SA True :=
  makeComparisonData _ _ U.mapDerivedCategory SB SA βB βA m.derived χ.derived

end CategoryTheory.RingedForgetTensorTransposition
