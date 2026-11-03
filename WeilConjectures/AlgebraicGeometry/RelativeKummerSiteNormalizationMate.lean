/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.KummerSiteAbelianEvaluation
public import WeilConjectures.CategoryTheory.Site.SiteModuleSheafConstantRingEquivalenceSupplement
public import WeilConjectures.CategoryTheory.ProperBaseChange.ModuleAbelianEvaluationComparison
public import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
public import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Category.ULift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonGlobalCohomologyFiniteNormalized
public import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ComparisonForgetScalars
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import Mathlib.Algebra.Polynomial.Laurent
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.Mathlib.RingTheory.Henselian
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.Sites.KummerNaturality
public import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
public import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackDegreeZero
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.AlgebraicGeometry.Exchange.ExchangeForgetCoefficients
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.StrictlyHenselianUnit
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.ClosedOpen
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Coinduce
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import WeilConjectures.AlgebraicGeometry.SiteComparisonEdgeSection2
public import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
public import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedDefinitions
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalDerivedImage
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.ProEtaleConstantDerivedEncoding
public import WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
public import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleTransportSupplement
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.Algebra.Homology.CochainComplexPlus
public import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleInverseImageCoherence
public import WeilConjectures.Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
public import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
public import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import WeilConjectures.CategoryTheory.SiteMorphismComposition
public import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.AlgebraicGeometry.PullbackCohomologyLongExactLadder
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.ProEtale.Comparison.ForgetUpperStar
import WeilConjectures.SixFunctors.ProEtale.ForgetModuleCohomology
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineDatum
import WeilConjectures.CategoryTheory.LeftModuleDerivedEvaluation.LeftModuleDerivedEvaluationForget
import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleTransportSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.CategoryTheory.Constant.ConstantLeftModuleInverseImageCoherence
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

private theorem q6_derived_mate_eq {C D C' D' : Type*} [Category* C] [Category* D]
    [Category* C'] [Category* D'] [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory C']
    [HasDerivedCategory D'] [EnoughInjectives D] [EnoughInjectives D']
    {l : C ⥤ D} {r : D ⥤ C} {p : C' ⥤ D'} {t : D' ⥤ C'}
    {a : C ⥤ C'} {b : D ⥤ D'} [l.Additive] [r.Additive] [p.Additive]
    [t.Additive] [a.Additive] [b.Additive]
    [PreservesFiniteLimits l] [PreservesFiniteColimits l]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p]
    [PreservesFiniteLimits a] [PreservesFiniteColimits a]
    [PreservesFiniteLimits b] [PreservesFiniteColimits b]
    (e : l ⊣ r) (d : p ⊣ t) (σ : a ⋙ p ≅ l ⋙ b) :
    let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
    Functor.rightDerivedFunctorPlusBaseChange (mateEquiv e d σ.hom).natTrans =
      (mateEquiv e.derivedPlus d.derivedPlus θ.hom).natTrans := by
  dsimp only
  let θ := (Functor.mapDerivedCategoryPlusCompIso a p).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫ Functor.mapDerivedCategoryPlusCompIso l b
  have hθ (N : HomotopyCategory.Plus C) :
      θ.hom.app (DerivedCategory.Plus.Qh.obj N) ≫
        D+(b).map (l.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        b.mapDerivedCategoryPlusFactorsh.hom.app (l.mapHomotopyCategoryPlus.obj N) =
      D+(p).map (a.mapDerivedCategoryPlusFactorsh.hom.app N) ≫
        p.mapDerivedCategoryPlusFactorsh.hom.app (a.mapHomotopyCategoryPlus.obj N) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus σ.hom).app N) := by
    simp only [θ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh l b N]
    rw [Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh σ N]
    rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh a p N]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  apply Functor.rightDerived_ext (R+(r) ⋙ D+(a))
    (Functor.whiskerRight r.rightDerivedFunctorPlusUnit D+(a) ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.Plus.quasiIso D)
  apply NatTrans.ext
  funext M
  have hf := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac
    (mateEquiv e d σ.hom).natTrans) M
  have hm := Adjunction.derivedPlus_mateEquiv_app_fac e d σ.hom θ.hom hθ M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hf ⊢
  rw [hf, hm]
  simp [Functor.rightDerivedFunctorPlusBaseChangeAux,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]

private theorem q6_underived_comparison_mate (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (f : U ⟶ V) :
    lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} A) =
      (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).hom).natTrans := by
  apply NatTrans.ext
  funext K
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  apply (cancel_epi ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f).inv.app
    ((Etale.lowerStar (ModuleCat.{u + 1} A) f).obj K))).1
  have h := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (lowerStarComparisonUpperStarBaseChange f (ModuleCat.{u + 1} A)) K
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (comparisonAdjunction (ModuleCat.{u + 1} A) V)
    (comparisonAdjunction (ModuleCat.{u + 1} A) U)
    (lowerStarCompComparisonLowerStarIso f (ModuleCat.{u + 1} A)).inv
  unfold lowerStarComparisonUpperStarBaseChange at h
  rw [hi] at h
  change _ = (comparisonUpperStarCompUpperStarIso
    (ModuleCat.{u + 1} A) f).hom.app _ ≫ _ at h
  simpa only [lowerStarComparisonUpperStarBaseChange, Category.assoc,
    Iso.inv_hom_id_app_assoc] using
    congrArg (fun t ↦ (comparisonUpperStarCompUpperStarIso
      (ModuleCat.{u + 1} A) f).inv.app ((Etale.lowerStar
        (ModuleCat.{u + 1} A) f).obj K) ≫ t) h

/-- The higher comparison mate is identified by the derived mate calculation.  The
underived comparison is the mate of the canonical inverse-image comparison; the
right-derived base-change mate then satisfies `unit_mateEquiv`.  Rewriting the two
recorded derived adjunctions gives the displayed equation for every `M`.
(blueprint: new-relative-kummer-site-normalization-mate). -/
theorem relativeKummerSiteNormalization_mate_fact {k : Type u} [Field k] [IsAlgClosed k]
    (ℓ N : ℕ) (hℓ : ℓ.Prime) (hN : 1 ≤ N) (hℓk : IsUnit (ℓ : k))
    (A : Type (u + 1)) [CommRing A] [Algebra (ZMod (ℓ ^ N)) A]
    [Module.Finite (ZMod (ℓ ^ N)) A] [Module.Free (ZMod (ℓ ^ N)) A]
  {X B : Scheme.{u}} (a : X ⟶ B) (_b : B ⟶ Spec (.of k))
      [QuasiCompact a] [QuasiSeparated a]
      (M : DerivedCategory.Plus (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))) :
  (comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) a).unit.app M) ≫
      (fixedComparisonDirectImageMatePlus A a).app
        ((Etale.upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategoryPlus.obj M) =
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) a).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus.obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) a).rightDerivedFunctorPlus.map
        ((fixedComparisonPullbackPlus A a).inv.app M) := by
  let σ := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) a
  let θ := (Functor.mapDerivedCategoryPlusCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} A) B)
    (upperStar (ModuleCat.{u + 1} A) a)).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso σ ≪≫
    Functor.mapDerivedCategoryPlusCompIso (Etale.upperStar (ModuleCat.{u + 1} A) a)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)
  let θsq : TwoSquare
      (comparisonUpperStar (ModuleCat.{u + 1} A) B).mapDerivedCategoryPlus
      (Etale.upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategoryPlus
      (upperStar (ModuleCat.{u + 1} A) a).mapDerivedCategoryPlus
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus :=
    { app := fun K => θ.hom.app K
      naturality := θ.hom.naturality }
  have hθsq : θsq = θ.hom := by
    apply NatTrans.ext
    funext K
    rfl
  have hm : fixedComparisonDirectImageMatePlus A a =
      (mateEquiv
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a).derivedPlus
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) a).derivedPlus
        θsq).natTrans := by
    unfold fixedComparisonDirectImageMatePlus
    rw [q6_underived_comparison_mate, q6_derived_mate_eq]
    rw [hθsq]
  have hθ : (fixedComparisonPullbackPlus A a).inv = θ.hom := by
    apply NatTrans.ext
    funext K
    apply (cancel_mono ((fixedComparisonPullbackPlus A a).hom.app K)).1
    have hσ : (Functor.mapDerivedCategoryPlusNatIso σ.symm).hom =
        (Functor.mapDerivedCategoryPlusNatIso σ).inv := by
      apply NatTrans.ext
      funext Z
      apply DerivedCategory.Plus.ι.map_injective
      rw [Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
        Functor.mapDerivedCategoryNatIso_symm]
      have h : DerivedCategory.Plus.ι.mapIso
          ((Functor.mapDerivedCategoryPlusNatIso σ).app Z) =
          (Functor.mapDerivedCategoryNatIso σ).app Z.obj :=
        Iso.ext (Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app σ Z)
      exact (congrArg Iso.inv h).symm
    have he : Functor.mapDerivedCategoryPlusNatIso σ.symm =
        (Functor.mapDerivedCategoryPlusNatIso σ).symm := Iso.ext hσ
    have hσ' : (Functor.mapDerivedCategoryPlusNatIso σ.symm).inv =
        (Functor.mapDerivedCategoryPlusNatIso σ).hom := congrArg Iso.inv he
    simp only [θ, fixedComparisonPullbackPlus, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, hσ, hσ', σ, Category.assoc,
      Iso.inv_hom_id_app_assoc]
  rw [hm]
  dsimp only [derivedUpperStarLowerStarAdjunctionPlus,
    Etale.derivedUpperStarLowerStarAdjunctionPlus]
  rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  rw [hθ]
  exact unit_mateEquiv _ _ θsq M

end AlgebraicGeometry.ProEtale
