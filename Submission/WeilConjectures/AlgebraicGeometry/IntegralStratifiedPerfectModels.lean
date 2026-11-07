/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.LocalizedSiteTensorRestriction
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Homology.BaseDerivedExtensionResolution
public import Submission.WeilConjectures.Algebra.Homology.BifunctorMappingConeNaturality
public import Submission.WeilConjectures.Algebra.Homology.BifunctorSingleNaturality
public import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsTensorCancellationIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.ExactProductsRoosComparison
public import Submission.WeilConjectures.Algebra.Homology.FilteredFreeKProjective
public import Submission.WeilConjectures.Algebra.Homology.FlatOpcyclesTorCriterion
public import Submission.WeilConjectures.Algebra.Homology.FlatTermKFlatFunctor
public import Submission.WeilConjectures.Algebra.Homology.KFlatScalarExtensionCounit
public import Submission.WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
public import Submission.WeilConjectures.Algebra.Homology.LargeFilteredFreeResolution
public import Submission.WeilConjectures.Algebra.Homology.RingedKFlatSingleTensorComparison
public import Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
public import Submission.WeilConjectures.AlgebraicGeometry.AdicCoefficientFiltration
public import Submission.WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplete
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientComparisonFiniteReflection
public import Submission.WeilConjectures.AlgebraicGeometry.CoefficientFpLocalSystemEtaleCover
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantDerivedNormalizationUniversal
public import Submission.WeilConjectures.AlgebraicGeometry.ConstantRealizationDerivedScalarExtension
public import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import Submission.WeilConjectures.AlgebraicGeometry.DerivedPullbackRepresentativeComputation
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteFreeConstantLocalLift
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSetsRepresentability
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFinitelyPresentedLocalModelsComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImageTensorComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLocalScalarHomologyIso
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleOriginFromFiniteModels
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveTowerDerivedLimit
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Submission.WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
public import Submission.WeilConjectures.AlgebraicGeometry.ScalarExtensionBinaryCoherence
public import Submission.WeilConjectures.AlgebraicGeometry.SequenceSiteCompletionProjection
public import Submission.WeilConjectures.AlgebraicGeometry.SiteBoundedConstantModel
public import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
public import Submission.WeilConjectures.CategoryTheory.AdditiveConeFamilyComparison
public import Submission.WeilConjectures.CategoryTheory.ConstantModuleFlat
public import Submission.WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor
public import Submission.WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
public import Submission.WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantSerre
public import Submission.WeilConjectures.CategoryTheory.FlatConstantTensorProZeroCones
public import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
public import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import Submission.WeilConjectures.CategoryTheory.SiteModuleSheafConstantRingEquivalence
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
public import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerTriangle
public import Submission.WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
public import Submission.WeilConjectures.ConstructibleSheaf.InternalHom
public import Submission.WeilConjectures.RingTheory.DerivedModuleScalarAdjunction
public import Submission.WeilConjectures.RingTheory.FiniteConeFreeModel
public import Submission.WeilConjectures.RingTheory.KoszulProjectiveResolution
public import Submission.WeilConjectures.RingTheory.NilpotentProjectiveComplexLift
public import Submission.WeilConjectures.RingTheory.NoetherianKoszulAugmentationProZero
public import Submission.WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel
public import Submission.WeilConjectures.RingTheory.PseudoCoherentIffAllM
public import Submission.WeilConjectures.RingTheory.RlimPerfectComplete
public import Submission.WeilConjectures.SecSmoothPurity.CochainComparisonMonoidalEquations
public import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
public import Submission.WeilConjectures.SecSmoothPurity.ModuleTensorMonoidalEquations
public import Submission.WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import Submission.WeilConjectures.SixFunctors.ProEtale.Adic.DerivedLowerStarDerivedLimit
public import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.EtaleOriginHomology
public import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
public import Submission.WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Completed integral constant models

(auxiliary; not a blueprint node).

Definitions and exact realization for the integral stratified-perfect characterization.
Source: Bhatt--Scholze, Propositions 6.6.11 and 6.8.11(3)
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

-- Universe-polymorphic `{max u (t + 1)}` sheafification instances get stuck on `{u + 1}` searches.
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
  AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective


namespace AlgebraicGeometry.Scheme

/-- The ordinary realization N ↦ A_T ⊗_A N, using the normalized coefficient comparison.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
def integralConstantModule (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : ModuleCat.{u + 1} A ⥤
      pbcModules T (pbcAdicCompletion T d) :=
  completedKoszulConstant T
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite } ⋙
    pbcRestrict (pbcCompletedComparison T d).inv

/-- Exactness of the ordinary completed-constant realization.
Source: Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11
(auxiliary; not a blueprint node).
Proof: constant module sheafification is exact. The completed ring is flat over
constant A by lem-weil-pbc-completed-constant-sheaf-reduction, since d is Noetherian.
Thus tensoring with it preserves finite limits and colimits. Restriction along the
normalized coefficient isomorphism is an exact equivalence. -/
theorem integralConstantModule_exact (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) :
    PreservesFiniteLimits (integralConstantModule T d) ∧
      PreservesFiniteColimits (integralConstantModule T d) := by
  let dd : ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  let K := adicLisseConstantModules T A
  let E := completedConstantExtension T (adicDatumScalar T dd)
  let R := pbcRestrict (pbcCompletedComparison T d).inv
  have hK : PreservesFiniteLimits K ∧ PreservesFiniteColimits K := by
    let P : ModuleCat.{u + 1} A ⥤
      _root_.PresheafOfModules.{u + 1}
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
      siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
        PresheafOfModules.pushforward₀
          ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
          ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))
    have hP : PreservesFiniteLimits P := by
      constructor
      intro J _ _
      constructor
      intro F
      constructor
      intro c hc
      exact ⟨_root_.PresheafOfModules.evaluationJointlyReflectsLimits _ _
        (fun X ↦ hc)⟩
    have hP' : PreservesFiniteColimits P := by
      constructor
      intro J _ _
      constructor
      intro F
      constructor
      intro c hc
      exact ⟨_root_.PresheafOfModules.evaluationJointlyReflectsColimits _ _
        (fun X ↦ hc)⟩
    let S : _root_.PresheafOfModules.{u + 1} ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) ⥤ _ :=
      PresheafOfModules.sheafification (adicLisseConstantUnit T A)
    exact ⟨comp_preservesFiniteLimits P S, comp_preservesFiniteColimits P S⟩
  have hE : PreservesFiniteLimits E ∧ PreservesFiniteColimits E := by
    let := dd.toCompleteCoefficientDatum.noetherian
    have h := completed_constant_algebra_flat_quotients T dd.ideal
      _ (Iso.refl _) (adicDatumScalar T dd) (by
        intro n
        exact (adicDatumScalar_exists T dd).exists.choose_spec n)
    have he := (exactFunctor_iff E).1 h.2.1
    exact ⟨he.1, he.2⟩
  let := hK.1
  let := hK.2
  let := hE.1
  let := hE.2
  exact ⟨comp_preservesFiniteLimits (K ⋙ E) R,
    comp_preservesFiniteColimits (K ⋙ E) R⟩

/-- Additivity of completed-constant realization, inherited from its two factors.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
instance integralConstantModule_additive (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : (integralConstantModule T d).Additive :=
  letI := (integralConstantModule_exact T d).1
  Functor.additive_of_preserves_binary_products _

/-- The derived realization P ↦ A_T ⊗^L_A P, obtained by localizing the exact
ordinary constant-module realization. On bounded finite projective complexes this
is its termwise tensor realization.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
def integralConstantDerived (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) : completedConstantDerived (ModuleCat.{u + 1} A) ⥤
      DerivedCategory (pbcModules T (pbcAdicCompletion T d)) :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  letI := (integralConstantModule_exact T d).1
  letI := (integralConstantModule_exact T d).2
  (integralConstantModule T d).mapDerivedCategory

/-- Restrict a derived object first to a stratum and then to a covering site object.
The slice coefficient sheaf is the restriction of the actual inverse-image ring.
Source: Bhatt--Scholze, Proposition 6.6.11; Stacks Tags 0997 and 0998
(auxiliary; not a blueprint node). -/
def integralLocalDerived {T S : Scheme.{u}} (g : S ⟶ T)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (pbcModules T R)) :
    completedConstantDerived (SheafOfModules.{u + 1}
      (((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)).over U)) :=
  ringedSiteDerivedRestrictionOfUniverses
    ((adicLisseForget S).obj ((adicTowerInverseImage g).obj R)) U
    ((adicTowerPullback g R).obj K)

/-- Condition (ii): finite strata, on each a pro-etale covering sieve, and on each
cover member an actual perfect A-complex whose completed realization is K there.
IsPerfectRingComplex is the recorded bounded finite-projective notion.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
def IsIntegralStratifiedPerfect (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A)
    (K : DerivedCategory (pbcModules T (pbcAdicCompletion T d))) : Prop :=
  ∃ s : Stratification T, ∀ i : Fin s.n,
    ∃ V : Sieve (⊤_ (s.domain i).ProEt),
      V ∈ ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
        ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
          ∃ P : completedConstantDerived (ModuleCat.{u + 1} A),
            @DerivedCategory.IsPerfectRingComplex A _
              (HasDerivedCategory.standard (ModuleCat.{u + 1} A)) P ∧
              Nonempty (integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) U K ≅
                integralLocalDerived (s.immersion i) (pbcAdicCompletion T d) U
                  ((integralConstantDerived T d).obj P))

/-- The constructible integral sheaf condition: finite strata and locally the ordinary
completed realization of a finitely presented A-module, including the zero module.
Source: Bhatt--Scholze, Definition 6.8.10
(auxiliary; not a blueprint node). -/
def IsIntegralStratifiedFinitelyPresented (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (F : pbcModules T (pbcAdicCompletion T d)) : Prop :=
  ∃ s : Stratification T, ∀ i : Fin s.n,
    ∃ V : Sieve (⊤_ (s.domain i).ProEt),
      V ∈ ProEt.topology (s.domain i) (⊤_ (s.domain i).ProEt) ∧
        ∀ (U : (s.domain i).ProEt) (f : U ⟶ ⊤_ (s.domain i).ProEt), V f →
          ∃ N : ModuleCat.{u + 1} A, Module.FinitePresentation A N ∧
            Nonempty ((SheafOfModules.overFunctor _ U).obj
              ((proEtaleModuleInverseImage (s.immersion i) (pbcAdicCompletion T d)).obj F) ≅
              (SheafOfModules.overFunctor _ U).obj
                ((proEtaleModuleInverseImage (s.immersion i) (pbcAdicCompletion T d)).obj
                  ((integralConstantModule T d).obj N)))

end AlgebraicGeometry.Scheme
