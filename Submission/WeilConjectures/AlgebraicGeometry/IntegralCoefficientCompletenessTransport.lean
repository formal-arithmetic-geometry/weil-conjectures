/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
public import Submission.WeilConjectures.Algebra.Homology.HomTensorDifferential
public import Submission.WeilConjectures.Algebra.Homology.KFlatTotalTensorModel
public import Submission.WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
public import Submission.WeilConjectures.Algebra.Homology.RingedInternalHomShiftOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import Submission.WeilConjectures.Algebra.Homology.RingedTensorComplexConstraints
public import Submission.WeilConjectures.Algebra.Homology.ScalarHomOrdinaryTensorComparison
public import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralDerivedReduction
public import Submission.WeilConjectures.AlgebraicGeometry.IntegralOperationsWellDefined
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
public import Submission.WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import Submission.WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHomComplex
public import Submission.WeilConjectures.CategoryTheory.DerivedCategory.ExactRestrictionComposition
public import Submission.WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
public import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
public import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import Submission.WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
import Submission.WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
import Submission.WeilConjectures.Algebra.Homology.KFlatResolution
import Submission.WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import Submission.WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
import all Submission.WeilConjectures.AlgebraicGeometry.CompletedAdicCoefficientDatum
import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
import Submission.WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
import Submission.WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import Submission.WeilConjectures.AlgebraicGeometry.PbcCompletedPullbackActual
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
import Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Submission.WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
import Submission.WeilConjectures.AlgebraicGeometry.SemilinearDerivedCalculus
import Submission.WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.CochainAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Submission.WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
import Submission.WeilConjectures.CategoryTheory.GeometricModuleConstruction
import Submission.WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import Submission.WeilConjectures.CategoryTheory.NatTransFromResolvingClass
import Submission.WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import Submission.WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import Submission.WeilConjectures.CategoryTheory.RingedNegativeKoszulDuality
import Submission.WeilConjectures.CategoryTheory.RingedSectionLocalizationOfUniverses
import Submission.WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import Submission.WeilConjectures.CategoryTheory.ScalarLocalizationRegularColimit
import Submission.WeilConjectures.CategoryTheory.StrictRoosDerivation
import Submission.WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Existence
import Submission.WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Data.Nat.Prime.Infinite

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Completeness under normalized integral coefficient transport

These coefficient equivalences and completeness comparisons are independent of
bounded constructibility and the stratified-perfect characterization.
Source: Stacks 099N; Bhatt--Scholze, Section 6.5
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

section CoefficientPresentation
variable (W : Scheme.{u})

/-- Lift the landed Ring-level coefficient comparison to commutative ring sheaves.
Its image under forgetting commutativity is the existing normalized comparison.
Source: Stacks 099N and Bhatt--Scholze 6.8.2(1)
(auxiliary; not a blueprint node).
Proof: a morphism between commutative rings is exactly a ring morphism. Thus the
forgetful functor on ring sheaves is fully faithful. Lift the existing comparison
and its inverse. Faithfulness gives their inverse identities and uniqueness. The
finite projection normalization is inherited from the landed comparison. -/
theorem purCoefficientIso_existsUnique :
    ∃! e : pbcAdicCompletion W (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E W,
      (adicLisseForget W).mapIso e = integralDetailedCoefficientComparison W l E := by
  let F := adicLisseForget W
  let hF := fullyFaithfulSheafCompose (ProEt.topology W)
    (Functor.FullyFaithful.ofFullyFaithful (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}))
  refine ⟨hF.preimageIso (integralDetailedCoefficientComparison W l E), ?_, ?_⟩
  · apply Iso.ext
    exact hF.map_preimage _
  · intro e he
    apply F.mapIso_injective
    apply Iso.ext
    exact (congrArg Iso.hom he).trans (hF.map_preimage _).symm

/-- The CommRing lift of integralDetailedCoefficientComparison, with no new choice
of normalization. Source: Stacks 099N
(auxiliary; not a blueprint node). -/
def purCoefficientIso := (purCoefficientIso_existsUnique l E W).exists.choose

end CoefficientPresentation

section RestrictionEquivalence
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  {R S : Sheaf J RingCat.{u + 1}}

end RestrictionEquivalence

end WeilConjectures
