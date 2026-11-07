/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Weil.WeilCompletedKoszulLimitComparison
import Submission.WeilConjectures.CategoryTheory.RingedCechKoszulComparisonOnSite
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

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Comparing the published Koszul fiber with Cech internal Hom

Source: Stacks Project, algebraization.tex, Tag 0A0E,
lemma-derived-completion-koszul, and sites-cohomology.tex, Tags 0941 and 0A0A.
(blueprint: lem-weil-pbc-completed-fiber-cech-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

/-- The published Koszul fiber is Cech internal Hom, with its specified unit.
Source: Stacks Project, Tag 0A0E
(blueprint: lem-weil-pbc-completed-fiber-cech-comparison).
Proof: compare the explicit fiber with the prescribed strict derived inverse limit.
The existing single-site Cech--Koszul theorem identifies that strict limit with
Cech internal Hom and carries the Cech unit to the strict unit. Compose the two
isomorphisms and cancel the second unit equation. -/
theorem completed_fiber_cech_comparison
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A)
    (C : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ) :
    let O := completedCechRing X d
    let F := completedCechDerivedEquiv X d
    let b := fun i ↦ completedCechScalar X d (a i)
    ∃ e : F.functor.obj (DerivedCategory.Q.obj (intrinsicCompletionComplex X d r a C)) ≅
        (ringedCechCompletionFunctor O (ringedExtendedCech O r b).1).obj
          (F.functor.obj (DerivedCategory.Q.obj C)),
      F.functor.map (DerivedCategory.Q.map (intrinsicCompletionComplexUnit X d r a C)) ≫
          e.hom =
        ringedCechCompletionUnit O (ringedExtendedCech O r b).1
          (ringedExtendedCech O r b).2 (F.functor.obj (DerivedCategory.Q.obj C)) := by
  let O := completedCechRing X d
  let F := completedCechDerivedEquiv X d
  let b := fun i ↦ completedCechScalar X d (a i)
  obtain ⟨D, theta, htheta⟩ := exists_ringed_cech_koszul_comparison_on_site O r b
  obtain ⟨e, he⟩ := completed_fiber_strict_limit_comparison X d r a C D
  refine ⟨e ≪≫ (theta.app (F.functor.obj (DerivedCategory.Q.obj C))).symm, ?_⟩
  dsimp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, he, ← htheta]
  change (_ ≫ theta.hom.app _) ≫ theta.inv.app _ = _
  rw [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry.Scheme
