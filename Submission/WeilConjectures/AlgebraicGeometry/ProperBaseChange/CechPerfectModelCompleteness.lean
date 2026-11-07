/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletion
import all Submission.WeilConjectures.AlgebraicGeometry.CechPerfectModel.CechPerfectComplexModel
import all Submission.WeilConjectures.AlgebraicGeometry.SfbPerfectModelComplexComparison
import all Submission.WeilConjectures.AlgebraicGeometry.SfbCompletionRingComparison
import all Submission.WeilConjectures.AlgebraicGeometry.Adic.AdicLisseModuleSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.CompletedConstantReduction.CompletedConstantSheafReductionSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
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
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Submission.WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import all Submission.WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
import all Submission.WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import all Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import all Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import all Submission.WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import all Submission.WeilConjectures.ConstructibleSheaf.Defs
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import all Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.Algebra.Homology.DerivedCategory.TStructure
import all Submission.WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfectData
import all Submission.WeilConjectures.AlgebraicGeometry.AdicPerfectModelCompleteReduction
import all Submission.WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
import all Submission.WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
import all Mathlib.Algebra.Category.Ring.FilteredColimits
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingInverseImage
import all Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement
import all Submission.WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import all Mathlib.CategoryTheory.Limits.Final
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.RingTheory.Noetherian.Defs
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Submission.WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import all Submission.WeilConjectures.CategoryTheory.RingedIdealGenerators
import all Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import all Submission.WeilConjectures.CategoryTheory.RingedDerivedRestriction
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import all Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import all Submission.WeilConjectures.CategoryTheory.RingedSectionLocalization
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.RingTheory.Localization.Away.Basic
import all Submission.WeilConjectures.AlgebraicGeometry.RingedTopoiTensorSections
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all Submission.WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all Submission.WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import all Mathlib.Algebra.Module.Projective
import all Mathlib.RingTheory.TensorProduct.Finite
import all Mathlib.RingTheory.Noetherian.Basic
import all Mathlib.Algebra.Category.ModuleCat.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Submission.WeilConjectures.AlgebraicGeometry.Torsion.TorsionLimitSheafCompletenessSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleMultiplicationDifferenceCriterionSupplement
import all Mathlib.RingTheory.Nilpotent.Lemmas
import all Submission.WeilConjectures.CategoryTheory.ConstantFiniteFreePresentationExtension
import all Submission.WeilConjectures.CategoryTheory.Site.SiteConstantModuleHomSupplement
import all Submission.WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import all Mathlib.Algebra.Category.ModuleCat.Products
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all Submission.WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionBinaryCoherenceSupplement
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all Submission.WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import all Submission.WeilConjectures.Algebra.Homology.FlatScalarRealizationFlat
import all Submission.WeilConjectures.Algebra.Homology.FlatScalarRealization
import all Mathlib.Algebra.Homology.Additive
import all Mathlib.RingTheory.Flat.Basic
import all Submission.WeilConjectures.CategoryTheory.ConstantModuleFlat
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all Submission.WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all Mathlib.RingTheory.Flat.EquationalCriterion
import all Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all Submission.WeilConjectures.Algebra.Homology.RingedSiteRestrictionKFlat
import all Submission.WeilConjectures.CategoryTheory.SiteCoveringAxioms
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import all Submission.WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import all Submission.WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
import all Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all Mathlib.CategoryTheory.Sites.LocallyInjective
import all Mathlib.CategoryTheory.Abelian.Exact
import all Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensor
import all Submission.WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
import all Submission.WeilConjectures.CategoryTheory.RingedSliceExtensionTensorHomData
import all Submission.WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import all Submission.WeilConjectures.Algebra.Homology.SixFunctors.LocalizedSiteTensorRestrictionSupplement
import all Mathlib.CategoryTheory.Sites.CoverLifting
import all Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import all Submission.WeilConjectures.AlgebraicGeometry.Completed.Constant.CompletedConstantCoefficientEquivalence
import all Submission.WeilConjectures.AlgebraicGeometry.IntegralCompletedConstantModelTransport
import all Submission.WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.CompletedConstantConstructibility
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all Submission.WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all Submission.WeilConjectures.AlgebraicGeometry.Integral.IntegralCriterionReductionsSupplement
import Submission.WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulConstantTransport

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Perfect constant complexes in the intrinsic coefficient presentation -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

-- imported instances such as `strictDvrSiteSmall` and `surjectiveTower_wEqualsLocallyBijective`
-- leave their coefficient universe free; pin the site smallness to `u + 1` and drop the other
private instance (priority := 10000) proEtaleSiteSmall (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.ProEt :=
  essentiallySmallSelf.{u + 1} _

attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

namespace CechPerfectModel

private local instance standardDerived {C : Type (u + 1)} [SmallCategory C]
    {J : GrothendieckTopology C} (O : Sheaf J CommRingCat.{u + 1}) :
    HasDerivedCategory (ConstantCompletion.Mod O) := HasDerivedCategory.standard _

attribute [local irreducible] normalizedComparison comparisonModulesEquiv

private def normalizedRealization (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) :
    integralConstantModule T d ⋙ (comparisonModulesEquiv T d).functor ≅
      commutativeSiteConstantModuleFunctor (completedCechTopology T) A ⋙
        ConstantCompletion.change
          (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal) := by
  let F := integralConstantModule T d
  let G := pbcRestrict (pbcCompletedComparison T d).hom
  let H := adicLisseConstantModules T A ⋙
    completedAdicChange T (CompletedConstantReduction.base T d.ideal)
  let S := toSmall ((adicLisseForget T).obj (adicLisseCompletedRing T d.ideal))
  let c := CechConstantAlgebra.completionIso T d.ideal
  let R := ConstantCompletion.res c.inv
  let M := commutativeSiteConstantModuleFunctor (completedCechTopology T) A ⋙
    ConstantCompletion.change
      (ConstantCompletion.coefficientMap (completedCechTopology T) A d.ideal)
  let e : H ⋙ S ≅ M ⋙ ConstantCompletion.res c.hom :=
    (Functor.associator _ _ _) ≪≫ cech_completedRealizationIso T A d.ideal ≪≫
      (Functor.associator _ _ _).symm
  exact Functor.isoWhiskerLeft F (normalizedComparison T d) ≪≫
    (Functor.associator F G (S ⋙ R)).symm ≪≫
    Functor.isoWhiskerRight (completedModelRoundTrip T d) (S ⋙ R) ≪≫
    (Functor.associator H S R).symm ≪≫ Functor.isoWhiskerRight e R ≪≫
    Functor.associator M (ConstantCompletion.res c.hom) R ≪≫
    Functor.isoWhiskerLeft M (scalarRestrictionEquivalence c).unitIso.symm ≪≫
    Functor.rightUnitor M

attribute [local irreducible] normalizedRealization cech_completedRealizationIso

private theorem realization_complete (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (d : AdicCoefficientDatum A)
    (P : completedConstantDerived (ModuleCat.{u + 1} A))
    (hP : @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _) P) :
    ConstantCompletion.IsComplete
      (ConstantCompletion.projection (completedCechTopology T) A d.ideal 0)
      ((comparisonModulesEquiv T d).mapDerivedCategory.functor.obj
        ((integralConstantDerived T d).obj P)) := by
  obtain ⟨D, lo, hi, hlo, hhi, hterms, ⟨e⟩⟩ := hP
  let F := integralConstantModule T d
  let E := comparisonModulesEquiv T d
  let := (integralConstantModule_exact T d).1
  let := (integralConstantModule_exact T d).2
  let c : (E.functor.mapHomologicalComplex (.up ℤ)).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj D) ≅
      AdicPerfectModel.model (completedCechTopology T) d.ideal D :=
    HomologicalComplex.Hom.isoOfComponents
      (fun q ↦ (normalizedRealization T d).app (D.X q))
      (by intro i j _; exact ((normalizedRealization T d).hom.naturality (D.d i j)).symm)
  let α := E.functor.mapDerivedCategory.mapIso (F.mapDerivedCategory.mapIso e) ≪≫
    E.functor.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app D) ≪≫
    E.functor.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso c
  have hc := cech_model_complete T d.ideal D (fun q ↦ ⟨(hterms q).2, (hterms q).1⟩)
  intro U f hf
  let : HasDerivedCategory.{u + 2} (SheafOfModules ((sheafCompose
      ((completedCechTopology T).over U) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        ((ConstantCompletion.completed (completedCechTopology T) A d.ideal).over U))) :=
    HasDerivedCategory.standard _
  exact (hc U f hf).of_iso
    ((derivedInternalHom.{u + 1, u + 2} ((completedCechTopology T).over U)
      ((ConstantCompletion.completed (completedCechTopology T) A d.ideal).over U)).mapIso
      ((Iso.refl _).prod ((ringedDerivedRestriction _ U).mapIso α)))

end CechPerfectModel

attribute [local instance] HasDerivedCategory.standard

/-- A perfect scalar complex has an invertible intrinsic completion unit after
completed constant realization.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication and Lemma 6.5.8.
(blueprint: lem-weil-pbc-cech-perfect-model-completeness).

Proof: realize finite projectives as retracts of finite sums of the coefficient
unit. The inverse-limit coefficient unit is complete on every slice, by the
multiplication-difference criterion and exact countable products on the pro-etale
site. This criterion holds termwise for finite projective retracts and hence for
the realized complex. Compare constant sheafification and scalar extension on the
AsSmall site by their universal properties. The finite-projection coefficient
comparison fixes each scalar and therefore identifies the Koszul units. The
constant-completion reflector criterion makes the transported unit invertible;
the exact derived equivalence reflects this property. -/
theorem cechPerfectModel_intrinsicComplete (T : Scheme.{u})
    {A : Type (u + 1)} [CommRing A] [IsNoetherianRing A]
    (d : AdicCoefficientDatum A)
    (P : completedConstantDerived (ModuleCat.{u + 1} A))
    (hP : @DerivedCategory.IsPerfectRingComplex A _ (HasDerivedCategory.standard _) P)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (C : CochainComplex (pbcModules T (pbcAdicCompletion T d)) ℤ)
    (eC : DerivedCategory.Q.obj C ≅ (integralConstantDerived T d).obj P) :
    IsDerivedCompleteIntrinsic T d r a ha ((integralConstantDerived T d).obj P) C eC := by
  let β := CechConstantAlgebra.algebraIso T d.ideal (pbcCompletedComparison T d)
  let E := comparisonModulesEquiv T d
  let F := E.mapDerivedCategory.functor
  let R := ConstantCompletion.res β.inv
  let : PreservesFiniteLimits (ConstantCompletion.res β.inv) :=
    (siteRestrictScalars_exact β.inv).1
  let : PreservesFiniteColimits (ConstantCompletion.res β.inv) :=
    (siteRestrictScalars_exact β.inv).2
  let : (ConstantCompletion.res β.inv).Additive :=
    Functor.additive_of_preserves_binary_products _
  let : (completedCechModulesEquiv T d).functor.IsEquivalence :=
    (completedCechModulesEquiv T d).isEquivalence_functor
  have : (completedCechModulesEquiv T d).functor.Additive :=
    Functor.additive_of_preserves_binary_products _
  let : PreservesFiniteLimits
      ((completedCechModulesEquiv T d).functor ⋙ R) :=
    comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits
      ((completedCechModulesEquiv T d).functor ⋙ R) :=
    comp_preservesFiniteColimits _ _
  let H := (completedCechModulesEquiv T d).functor ⋙ R
  let σ : E.functor ≅ H := comparisonModulesEquiv_to_cech T d
  let : PreservesFiniteLimits H := preservesFiniteLimits_of_natIso σ
  let : PreservesFiniteColimits H := preservesFiniteColimits_of_natIso σ
  let δ : F ≅ (completedCechDerivedEquiv T d).functor ⋙ ConstantCompletion.dres β.inv :=
    Functor.mapDerivedCategoryNatIso σ ≪≫
      (Functor.mapDerivedCategoryCompIso (completedCechModulesEquiv T d).functor R).symm
  obtain ⟨c, hc⟩ := completed_koszul_constant_transport T d β
    (comparisonCompletedRingIso_scalar T d) F δ r a ha C
  have hcomplete := CechPerfectModel.realization_complete T d P hP
  have hC : ConstantCompletion.IsComplete
      (ConstantCompletion.projection (completedCechTopology T) A d.ideal 0)
      (F.obj (DerivedCategory.Q.obj C)) := by
    intro U f hf
    exact (hcomplete U f hf).of_iso
      ((derivedInternalHom.{u + 1, u + 2} ((completedCechTopology T).over U)
        ((ConstantCompletion.completed (completedCechTopology T) A d.ideal).over U)).mapIso
        ((Iso.refl _).prod ((ringedDerivedRestriction _ U).mapIso (F.mapIso eC))))
  obtain ⟨_, _, _, _, hiff⟩ := ConstantCompletion.koszul_quotient_reflector
    (completedCechTopology T) A d.ideal true r a ha
  have hu := (hiff (F.obj (DerivedCategory.Q.obj C))).mpr hC
  have hm : IsIso (F.map (DerivedCategory.Q.map
      (intrinsicCompletionComplexUnit T d r a C))) := by
    apply (isIso_comp_right_iff _ c.hom).mp
    rw [hc]
    exact hu
  have : IsIso (DerivedCategory.Q.map (intrinsicCompletionComplexUnit T d r a C)) :=
    (isIso_iff_of_reflects_iso _ F).mp hm
  unfold IsDerivedCompleteIntrinsic intrinsicCompletionUnit
  infer_instance

end AlgebraicGeometry.Scheme
