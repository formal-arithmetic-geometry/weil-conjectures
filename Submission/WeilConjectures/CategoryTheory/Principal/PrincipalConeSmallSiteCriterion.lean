/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.Algebra.Homology.PrincipalConeTower
public import Submission.WeilConjectures.CategoryTheory.Ringed.RingedPrincipalLocalTests
import Submission.WeilConjectures.AlgebraicGeometry.PrincipalConeKoszulRoosComparison
import Submission.WeilConjectures.CategoryTheory.Principal.PrincipalIdealLocalTestCriterion
import Submission.WeilConjectures.CategoryTheory.RingedKoszulCompletionReflector
import Submission.WeilConjectures.CategoryTheory.RingedKoszulSystem
import Submission.WeilConjectures.CategoryTheory.RingedExtendedCech
import Submission.WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import Submission.WeilConjectures.Algebra.Homology.HomComplex
import Submission.WeilConjectures.CategoryTheory.RingedCompletionUnit
import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestriction
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import Submission.WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import Submission.WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import Submission.WeilConjectures.CategoryTheory.RingedIdealGenerators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Submission.WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
import Submission.WeilConjectures.CategoryTheory.RingedCechKoszulDualKFlat
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Submission.WeilConjectures.Algebra.Homology.FiniteFreeZeroHomologyEvaluationIso
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison
import Submission.WeilConjectures.CategoryTheory.RingedCechKoszulColimitIso
import Submission.WeilConjectures.Algebra.Homology.InternalHom
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.CategoryTheory.Limits.Preserves.Bifunctor
import Submission.WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import Submission.WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Submission.WeilConjectures.CategoryTheory.RingedKoszulColimitHomOrdinaryLimit
import Submission.WeilConjectures.CategoryTheory.RingedHomComplexColimitCone
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Submission.WeilConjectures.CategoryTheory.RingedKoszulFiniteEvaluation
import Submission.WeilConjectures.CategoryTheory.RingedKoszulDualizable
import Submission.WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Submission.WeilConjectures.Algebra.Homology.Monoidal.Dual
import Submission.WeilConjectures.CategoryTheory.Monoidal.Dualizable
import Submission.WeilConjectures.CategoryTheory.RingedHomTensorUnitNormalization
import Submission.WeilConjectures.CategoryTheory.RingedComplexTensorEvaluation
import Submission.WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Submission.WeilConjectures.CategoryTheory.RingedKoszulTensorTowerLimitAcyclic
import Submission.WeilConjectures.CategoryTheory.RingedKoszulRoosInclusion
import Submission.WeilConjectures.CategoryTheory.ExactProductsRoos.ExactProductsRoosComparisonSupplement
import Submission.WeilConjectures.CategoryTheory.RingedKoszulFiniteHomTower
import Submission.WeilConjectures.Algebra.Homology.TelescopeHomRoosArrow
import Submission.WeilConjectures.Algebra.Homology.TelescopeColimit
import Submission.WeilConjectures.CategoryTheory.SignedDoubleHomCone.SignedDoubleHomConeSupplement
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomCoproduct
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Submission.WeilConjectures.Algebra.Homology.SplitPerfectTensorKInjective
import Mathlib.Algebra.Homology.BifunctorShift
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Submission.WeilConjectures.CategoryTheory.Monoidal.Rigid.Flat
import Submission.WeilConjectures.FromJoel.Algebra.Homology.HomotopyCategory.Monoidal
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalFree
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
import Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.CategoryTheory.ProperBaseChange.ExtendedCechCompletionModelSupplement
import Submission.WeilConjectures.CategoryTheory.RingedAugmentedCechRestriction
import Submission.WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
import Submission.WeilConjectures.CategoryTheory.LocalizationRHom.RingedLocalizationRestrictionSupplement
import Submission.WeilConjectures.Algebra.Homology.SliceTensorNatural
import Submission.WeilConjectures.Algebra.Homology.SliceModuleSheafification
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import all Submission.WeilConjectures.CategoryTheory.UnitPowerCompleteness

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # The principal cone criterion on a small ringed site
Source: Stacks 0999, 099B, 0A0E and 0941.
(blueprint: lem-pur-principal-cone-small-site-criterion). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false in
private theorem complete_of_iso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [∀ U : C, HasDerivedCategory.{w} (ringedSiteModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]
    (I : ringedSiteModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    (ι : I ⟶ SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))
    {N M : ringedSiteDerived O} (e : N ≅ M)
    (hN : IsLocallyDerivedRingedIdealComplete O I ι N) :
    IsLocallyDerivedRingedIdealComplete O I ι M := by
  intro U f hf
  let H := derivedInternalHom (J.over U) (O.over U)
  exact (hN U f hf).of_iso
    (H.mapIso ((Iso.refl _).prod ((ringedDerivedRestriction O U).mapIso e))).symm
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "Rg" => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "A" => SheafOfModules.{u} Rg
variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]
  [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u} ((Rg).over U))]
  [HasExactLimitsOfShape (Discrete ℕ) A]

attribute [local irreducible] CochainComplex.PrincipalCone.completion
  CochainComplex.PrincipalCone.unit
attribute [local irreducible] principalKoszulRoosUnit roosF koszulTowerComplex koszulTensorTower

/-- Singleton Koszul completion is the normalized principal cone completion.
Source: Stacks 0999, 099B, 0A0E and 0941.
(blueprint: lem-pur-principal-cone-small-site-criterion).
Proof: the image ideal of scalar multiplication has precisely the locally divisible
sections. Apply the singleton Koszul completion reflector to this image ideal, whose
one-element generating list follows from the image factorization. The comparison with
the strict tensor Koszul Roos complex and then the principal cone Roos complex preserves
the degree-zero unit. Transport output completeness across these comparisons. Their
unit equality identifies the reflector's invertibility criterion with the stated one. -/
theorem principalConeSmallSiteCriterion
    (a : (R.obj ⋙ forget CommRingCat).sections) (P : CochainComplex A ℤ) (μ : End P)
    (hμ : ∀ (q : ℤ) (U : Cᵒᵖ) (x : (P.X q).val.obj U),
      (μ.f q).val.app U x = @SMul.smul _ _ ((P.X q).val.obj U).isModule.toSMul (a.val U) x) :
    principalLocallyComplete.{u, u, u, w} R a
        ((DerivedCategory.Q.{w} (C := A)).obj (CochainComplex.PrincipalCone.completion μ)) ∧
      (principalLocallyComplete.{u, u, u, w} R a ((DerivedCategory.Q.{w} (C := A)).obj P) ↔
        IsIso ((DerivedCategory.Q.{w} (C := A)).map (CochainComplex.PrincipalCone.unit μ))) := by
  let := principalLocalTestSliceDerived R
  let I := image (ringedKoszulScalar R a)
  let ι := image.ι (ringedKoszulScalar R a)
  obtain ⟨D, hC, _, hcrit, _⟩ := ringedKoszulCompletionReflector R 1 (fun _ ↦ a)
    I ι (principal_generators R a)
  let b : (SheafOfModules.unit Rg).sections := ⟨a.val, a.property⟩
  obtain ⟨c, hc⟩ := principalConeKoszulRoosComparison R P a μ hμ
  obtain ⟨d, hd⟩ := principalKoszulRoos_presentation_comparison R b P D
  let e := c ≪≫ d
  have he : (DerivedCategory.Q.{w} (C := A)).map (CochainComplex.PrincipalCone.unit μ) ≫ e.hom =
      D.unit ((DerivedCategory.Q.{w} (C := A)).obj P) := by
    change _ ≫ c.hom ≫ d.hom = _
    rw [← Category.assoc, hc]
    simpa only [b] using hd
  refine ⟨(principalLocallyComplete_iff R a _).mpr
    (complete_of_iso R I ι e.symm (hC _)), ?_⟩
  rw [principalLocallyComplete_iff R a _, ← hcrit, ← he]
  exact isIso_comp_right_iff _ e.hom

end CategoryTheory
