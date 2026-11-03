/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.GeneralFieldFiniteDualizingTowers.GeneralFieldFiniteDualizingTowerData

import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.SequentialDerivedTowerLifting
import WeilConjectures.AlgebraicGeometry.Picard.GeneralFieldFiniteDualizingTowers.GeneralFieldNormalizedTowerComparison
import WeilConjectures.AlgebraicGeometry.Picard.GeneralFieldFiniteDualizingTowers.GeneralFieldNormalizedTowerCoherence
import WeilConjectures.AlgebraicGeometry.Picard.GeneralFieldFiniteDualizingTowers.GeneralFieldFullUniformizerRestriction
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SectionwiseFlatScalarModelExact
import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeSectionBasis
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.AlgebraicGeometry.FiniteDualizingNegativeSelfHom
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.MorphismProperty.Comma
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Types.ColimitType
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBoundedBelow


/-! # Coherent finite dualizing coefficient tower comparisons

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/`
`lem-coef-integral-finite-extension.proof.md`, coherent-tower and coherence paragraphs.
(blueprint: lem-sf-finite-dualizing-coefficient-tower-map)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.FiniteCoefficientAdjoints
open WeilConjectures.FiniteDualizingTowers
namespace WeilConjectures.GeneralFieldFiniteDualizingTowers
section Helpers
attribute [local implicit_reducible] rings omega atLevel constantRing realization
  evaluationBridge strictLevel Functor.ofOpSequence Functor.ofSequence
  Equivalence.mapDerivedCategory
  SheafOfModules.systemRingHasDerived
  AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory
set_option backward.defeqAttrib.useBackward true
variable (k : Type u) [Field k] (X : Scheme.{u})
  [X.Over (Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
  [QuasiCompact (X ↘ Spec (.of k))] [IsSeparated (X ↘ Spec (.of k))]
variable {l : ℕ} [Fact l.Prime] {E : Type (u + 1)} [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The object in strict-system coordinates, through the exact sequence equivalence.
Source: blueprint paragraph 4
(blueprint: lem-sf-finite-dualizing-coefficient-tower-map). -/
private abbrev strictObj {s : Stage l E} (P : Realization k X s) :=
  (SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1}
    (rings X s)).inverse.mapDerivedCategory.obj P.obj

private theorem strictLevel_transition {s : Stage l E} (P : Realization k X s)
    (n : ℕ) :
    HEq ((SheafOfModules.systemDerivedTransition.{u + 1, u, u + 1}
        (rings X s) (Nat.le_succ n)).app (strictObj k X P) ≫
      (SheafOfModules.systemRestriction.{u + 1, u, u + 1}
        (rings X s) (Nat.le_succ n)).mapDerivedCategory.map
          (strictLevel k X P n).hom)
      ((strictLevel k X P (n + 1)).hom ≫
        counitAdjunct k X (quotient s (Nat.le_succ n))) := by
  simpa only [strictObj, strictLevel, Iso.trans_hom, Iso.app_hom, Category.assoc]
    using P.transition n

private theorem finiteOmega_common_lower_bound :
    ∃ a : ℤ, ∀ (A : Type (u + 1)) [CommRing A] [Finite A],
      (finiteOmega k X A).IsGE a := by
  let := (compactification k X).hasCompactification
  let c := HasCompactification.compactification (X ↘ Spec (.of k))
  obtain ⟨d, hd⟩ :=
    exists_topologicalKrullDim_le_of_isPullback_of_compactSpace c.g
  refine ⟨-(2 * (d : ℤ)), ?_⟩
  intro A _ _
  have hvan : ∀ (G : Sheaf c.Z.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℕ),
      2 * d < q → IsZero
        ((((Etale.lowerStar (ModuleCat.{u + 1} A) c.g).rightDerived q).obj G)) := by
    intro G q hq
    apply Etale.isZero_of_forall_isZero_upperStar_algClosurePoint A _
    intro t
    exact Etale.isZero_upperStar_rightDerived_lowerStar_of_isProper_of_le
      A isAddTorsion_of_finite c.g t d
      (hd _ _ _ _ (IsPullback.of_hasPullback c.g _)) G q hq
  have hcompact : ∀ (K : DerivedCategory
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) (n : ℤ),
      K.IsLE n → ((Etale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} A) c).obj K).IsLE (n + 2 * (d : ℤ)) := by
    intro K n hK
    let := hK
    have : ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A)
        c.i).mapDerivedCategory.obj K).IsLE n :=
      Functor.isLE_mapDerivedCategory_obj _ K n
    exact (Etale.lowerStar (ModuleCat.{u + 1} A) c.g).isLE_rightDerivedFunctor_obj
      (2 * d) hvan _ n
  have hunit : (𝟙_ (Etale.DerivedCategoryModule A (Spec (.of k)))).IsGE 0 :=
    DerivedCategory.TStructure.t.isGE_of_iso
      (DerivedCategory.singleFunctorObjUnitIso _) 0
  let := hunit
  have he := (Etale.rightDerivedUpperShriekOfCompactificationAdjunction A c).isGE_obj_of_isLE
    DerivedCategory.TStructure.t DerivedCategory.TStructure.t (2 * (d : ℤ))
    hcompact (𝟙_ (Etale.DerivedCategoryModule A (Spec (.of k)))) 0
  have : (Etale.dualizingComplex A (X ↘ Spec (.of k))).IsGE (-(2 * (d : ℤ))) := by
    simpa only [Etale.dualizingComplex, Etale.rightDerivedUpperShriek, zero_sub] using he
  exact Functor.isGE_mapDerivedCategory_obj
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X) _ _

private theorem adjacentRestriction_obj_eq (s : Stage l E) (n : ℕ) :
    (res X (quotient s (Nat.le_succ n)).ringMap).mapDerivedCategory.obj (omega k X s n) =
      (SheafOfModules.SequentialDerived.adjacentRestriction (rings X s) n).obj
        (omega k X s n) := by
  dsimp only [omega, SheafOfModules.systemLevel,
    SheafOfModules.systemRingHasDerived, Scheme.reductionModulesHasDerivedCategory]
  simp only [res, SheafOfModules.SequentialDerived.adjacentRestriction,
    SheafOfModules.systemRestriction, rings, Functor.ofOpSequence_obj,
    Functor.ofOpSequence_map_homOfLE_succ]

private def adjacentCounit (s : Stage l E) (n : ℕ) :
    omega k X s (n + 1) ⟶
      (SheafOfModules.SequentialDerived.adjacentRestriction (rings X s) n).obj
        (omega k X s n) :=
  counitAdjunct k X (quotient s (Nat.le_succ n)) ≫
    eqToHom (adjacentRestriction_obj_eq k X s n)

/-- Composition preserves the specified adjacent quotient-map transport. -/
private theorem adjacentCounit_comp_heq (s : Stage l E) (n : ℕ)
    {M : DerivedCategory (SheafOfModules.systemLevel.{u + 1, u, u + 1}
      (rings X s) (n + 1))} (f : M ⟶ omega k X s (n + 1)) :
    HEq (f ≫ adjacentCounit k X s n)
      (f ≫ counitAdjunct k X (quotient s (Nat.le_succ n))) := by
  simpa only [adjacentCounit, Category.assoc] using
    comp_eqToHom_heq (f ≫ counitAdjunct k X (quotient s (Nat.le_succ n)))
      (adjacentRestriction_obj_eq k X s n)

private theorem realization_exists (s : Stage l E) : Nonempty (Realization k X s) := by
  obtain ⟨a, ha⟩ := finiteOmega_common_lower_bound k X
  have hb : ∀ n : ℕ, (omega k X s n).IsGE a := by
    intro n
    have := ha (atLevel s n).ring
    exact Functor.isGE_mapDerivedCategory_obj _ _ _
  obtain ⟨M, e, he⟩ :=
    (SheafOfModules.SequentialDerived.sequentialSemilinearDerivedDiagrams (rings X s)).1
      (omega k X s) (adjacentCounit k X s) ⟨a, hb⟩
  let d := (SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1}
    (rings X s)).mapDerivedCategory
  let obj := d.functor.obj M
  let w : d.inverse.obj obj ≅ M := (d.unitIso.app M).symm
  let level (n : ℕ) : (evaluation X s n).obj obj ≅ omega k X s n :=
    ((evaluationBridge X s n).app obj).symm ≪≫
      (SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1}
        (rings X s) n).mapIso w ≪≫ e n
  have hl (n : ℕ) : (evaluationBridge X s n).hom.app obj ≫ (level n).hom =
      (SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1}
        (rings X s) n).map w.hom ≫ (e n).hom := by
    simp only [level, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom,
      Iso.hom_inv_id_app_assoc]
  refine ⟨⟨obj, level, ?_⟩⟩
  intro n
  have h : (SheafOfModules.systemDerivedTransition.{u + 1, u, u + 1}
        (rings X s) (Nat.le_succ n)).app (d.inverse.obj obj) ≫
      (SheafOfModules.SequentialDerived.adjacentRestriction (rings X s) n).map
        ((evaluationBridge X s n).hom.app obj ≫ (level n).hom) =
    ((evaluationBridge X s (n + 1)).hom.app obj ≫ (level (n + 1)).hom) ≫
      adjacentCounit k X s n := by
    rw [hl n, hl (n + 1)]
    simp only [Functor.map_comp, Category.assoc]
    have hw := (SheafOfModules.systemDerivedTransition.{u + 1, u, u + 1}
      (rings X s) (Nat.le_succ n)).naturality w.hom
    simp only [Functor.comp_map] at hw
    rw [← reassoc_of% hw, he n]
  have hh := h.heq.trans (adjacentCounit_comp_heq k X s n
    ((evaluationBridge X s (n + 1)).hom.app obj ≫ (level (n + 1)).hom))
  simpa only [d, Equivalence.mapDerivedCategory, CategoryTheory.Equivalence.mk,
    Category.assoc] using hh

private theorem realization_common_lower_bound {s : Stage l E} (P : Realization k X s) :
    SheafOfModules.SequentialDerived.HasCommonLowerBound.{u + 1, u, u + 1}
      (rings X s) (strictObj k X P) := by
  obtain ⟨a, ha⟩ := finiteOmega_common_lower_bound k X
  refine ⟨a, fun n ↦ ?_⟩
  have := ha (atLevel s n).ring
  have : (omega k X s n).IsGE a := Functor.isGE_mapDerivedCategory_obj _ _ _
  exact DerivedCategory.TStructure.t.isGE_of_iso (strictLevel k X P n).symm a

private theorem realization_isEquivalence (A : Type (u + 1)) [CommRing A] :
    (realization X A).IsEquivalence := by
  exact ProEtale.intrinsicRealization_isEquivalence (Scheme.ProEt.topology X)
    A _ (scalarUnit X A)

private theorem finiteOmega_negative_self_hom
    (p : ℕ) (hp : p.Prime) (hchar : ringChar k = p)
    (hk : Finite k ∨ IsAlgClosed k) (hl : l ≠ p) (s : Stage l E) :
    Subsingleton (finiteOmega k X s.ring ⟶ (finiteOmega k X s.ring)⟦(-1 : ℤ)⟧) := by
  obtain ⟨e, _z, _hz, hI, _he⟩ := stage_ramification s
  have hn : 1 ≤ (e : ℕ) * (s.exponent : ℕ) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero e.ne_zero s.exponent.ne_zero)
  have h := Etale.finiteDualizing_negative_self_hom k p l hp hchar hk hl
    s.field (X ↘ Spec (.of k)) ((e : ℕ) * (s.exponent : ℕ)) hn
  have hJ : s.ideal =
      Padic.coefficientExtensionIdeal l s.field ((e : ℕ) * (s.exponent : ℕ)) :=
    hI (s.exponent : ℕ)
  let property (I : Ideal s.integers) : Prop :=
    ∀ [Finite (s.integers ⧸ I)],
      Subsingleton (finiteOmega k X (s.integers ⧸ I) ⟶
        (finiteOmega k X (s.integers ⧸ I))⟦(-1 : ℤ)⟧)
  have hP : property (Padic.coefficientExtensionIdeal l s.field
      ((e : ℕ) * (s.exponent : ℕ))) := by
    intro _
    exact h
  have hQ : property s.ideal := by
    rw [hJ]
    exact hP
  exact @hQ inferInstance

private theorem coefficient_annihilator (s : Stage l E) :
    ∃ n : ℕ, ∀ x : s.ring, (l ^ n : s.ring) * x = 0 := by
  obtain ⟨e, _z, _hz, hI, _he⟩ := stage_ramification s
  let r := (e : ℕ) * (s.exponent : ℕ)
  have h := (Padic.extension_integers_dvr l s.field
    (Padic.coefficientExtensionAbsoluteValue l s.field)
    (spectralNorm_extends (K := Padic l) (L := s.field))).choose_spec.choose_spec
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l s.field} :
      Set s.integers) = Padic.coefficientExtensionMaximalIdeal l s.field :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hell : (l : s.integers) ∈ Padic.coefficientExtensionMaximalIdeal l s.field := by
    apply (h.2.1 _).mpr
    change spectralNorm (Padic l) s.field (l : s.field) < 1
    rw [← map_natCast (algebraMap (Padic l) s.field) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hm : (l : s.integers) ^ r ∈ s.ideal := by
    rw [Stage.ideal, hI]
    change (l : s.integers) ^ r ∈
      Ideal.span ({Padic.coefficientExtensionUniformizer l s.field} : Set s.integers) ^ r
    rw [hgen]
    exact Ideal.pow_mem_pow hell r
  have hz : (l ^ r : s.ring) = 0 := by
    simpa only [map_pow, map_natCast] using Ideal.Quotient.eq_zero_iff_mem.mpr hm
  exact ⟨r, fun x ↦ by rw [hz, zero_mul]⟩

private theorem finiteOmega_restricted_negative_hom
    (p : ℕ) (hp : p.Prime) (hchar : ringChar k = p)
    (hk : Finite k ∨ IsAlgClosed k) (hl : l ≠ p)
    {s t : Stage l E} (a : Arrow s t) :
    Subsingleton (finiteOmega k X s.ring ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a.ringMap).obj
        ((finiteOmega k X t.ring)⟦(-1 : ℤ)⟧)) := by
  let := (compactification k X).hasCompactification
  let adj := @FiniteCoefficientOrdinary.scalarAdjunction.{u} X.ProEt inferInstance
    (essentiallySmallSelf.{0, u, u + 1} _) (Scheme.ProEt.topology X) s.ring t.ring
    inferInstance inferInstance a.ringMap
  let f := Etale.generalFieldFiniteProDualizingMap a.ringMap (X ↘ Spec (.of k))
  let := (Etale.generalFieldFiniteDualizingCoefficientChange k p l hp hchar hk
    (Fact.out : l.Prime) hl (a := X ↘ Spec (.of k))
    (coefficient_annihilator s) (coefficient_annihilator t)
    a.ringMap).pro_isIso
  let := finiteOmega_negative_self_hom k X p hp hchar hk hl t
  let e := adj.homEquiv (finiteOmega k X s.ring) ((finiteOmega k X t.ring)⟦(-1 : ℤ)⟧)
  let F : (finiteOmega k X s.ring ⟶
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a.ringMap).obj
        ((finiteOmega k X t.ring)⟦(-1 : ℤ)⟧)) →
      (finiteOmega k X t.ring ⟶ (finiteOmega k X t.ring)⟦(-1 : ℤ)⟧) :=
    fun g ↦ inv f ≫ e.symm g
  have hF : Function.Injective F := by
    intro g h he
    apply e.symm.injective
    exact (cancel_epi (inv f)).1 he
  exact hF.subsingleton

private theorem intrinsic_restricted_negative_hom
    (p : ℕ) (hp : p.Prime) (hchar : ringChar k = p)
    (hk : Finite k ∨ IsAlgClosed k) (hl : l ≠ p)
    {s t : Stage l E} (a : Arrow s t) :
    Subsingleton
      ((realization X s.ring).mapDerivedCategory.obj (finiteOmega k X s.ring) ⟶
        (res X a.ringMap).mapDerivedCategory.obj
          (((realization X t.ring).mapDerivedCategory.obj
            (finiteOmega k X t.ring))⟦(-1 : ℤ)⟧)) := by
  let F := (realization X s.ring).mapDerivedCategory
  let G := (realization X t.ring).mapDerivedCategory
  let R := (res X a.ringMap).mapDerivedCategory
  let W := finiteOmega k X t.ring
  let := realization_isEquivalence X s.ring
  let := finiteOmega_restricted_negative_hom k X p hp hchar hk hl a
  let e := (R.mapIso ((G.commShiftIso (-1)).app W)).symm ≪≫
    (derivedRestriction X a.ringMap).app (W⟦(-1 : ℤ)⟧)
  let eF := Equiv.ofBijective
    (fun f : finiteOmega k X s.ring ⟶
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) a.ringMap).obj
          (W⟦(-1 : ℤ)⟧) ↦ F.map f) ⟨F.map_injective, F.map_surjective⟩
  exact ((Iso.homCongr (Iso.refl _) e).trans eF.symm).injective.subsingleton

private theorem identification_hom_ext {s : Stage l E} (P Q : Realization k X s)
    (hP : SheafOfModules.SequentialDerived.HasCommonLowerBound.{u + 1, u, u + 1} (rings X s)
      (strictObj k X P))
    (hQ : SheafOfModules.SequentialDerived.HasCommonLowerBound.{u + 1, u, u + 1} (rings X s)
      (strictObj k X Q))
    (hs : ∀ n : ℕ, Subsingleton
      ((SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1}
          (rings X s) (n + 1)).obj (strictObj k X P) ⟶
        (SheafOfModules.SequentialDerived.adjacentRestriction (rings X s) n).obj
          (((SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1}
            (rings X s) n).obj (strictObj k X Q))⟦(-1 : ℤ)⟧)))
    (f g : P.obj ⟶ Q.obj)
    (h : ∀ n : ℕ, (evaluation X s n).map f = (evaluation X s n).map g) : f = g := by
  let F := (SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1}
    (rings X s)).inverse.mapDerivedCategory
  apply F.map_injective
  apply SheafOfModules.SequentialDerived.hom_ext_of_negative_hom.{u + 1, u, u + 1}
    (rings X s) (strictObj k X P) (strictObj k X Q) hP hQ hs
  intro n
  apply (cancel_mono ((evaluationBridge X s n).hom.app Q.obj)).1
  have hf := (evaluationBridge X s n).hom.naturality f
  have hg := (evaluationBridge X s n).hom.naturality g
  change (SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1}
    (rings X s) n).map (F.map f) ≫ _ = _ at hf
  change (SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1}
    (rings X s) n).map (F.map g) ≫ _ = _ at hg
  rw [hf, hg, h n]

private theorem strict_identification_compatible {s : Stage l E}
    (P Q : Realization k X s) (n : ℕ) :
    (SheafOfModules.systemDerivedTransition.{u + 1, u, u + 1}
        (rings X s) (Nat.le_succ n)).app (strictObj k X P) ≫
      (SheafOfModules.SequentialDerived.adjacentRestriction (rings X s) n).map
        ((strictLevel k X P n ≪≫ (strictLevel k X Q n).symm).hom) =
    (strictLevel k X P (n + 1) ≪≫ (strictLevel k X Q (n + 1)).symm).hom ≫
      (SheafOfModules.systemDerivedTransition.{u + 1, u, u + 1}
        (rings X s) (Nat.le_succ n)).app (strictObj k X Q) := by
  have hP := strictLevel_transition k X P n
  have hQ := strictLevel_transition k X Q n
  have hP' := eq_of_heq (hP.trans
    (adjacentCounit_comp_heq k X s n (strictLevel k X P (n + 1)).hom).symm)
  have hQ' := eq_of_heq (hQ.trans
    (adjacentCounit_comp_heq k X s n (strictLevel k X Q (n + 1)).hom).symm)
  apply (cancel_mono
    ((SheafOfModules.SequentialDerived.adjacentRestriction (rings X s) n).map
      (strictLevel k X Q n).hom)).1
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hP', hQ']
  simp only [Iso.inv_hom_id_assoc]

private theorem strict_negative_hom
    (p : ℕ) (hp : p.Prime) (hchar : ringChar k = p)
    (hk : Finite k ∨ IsAlgClosed k) (hl : l ≠ p) {s : Stage l E}
    (P Q : Realization k X s) (n : ℕ) :
    Subsingleton
      ((SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1}
          (rings X s) (n + 1)).obj (strictObj k X P) ⟶
        (SheafOfModules.SequentialDerived.adjacentRestriction (rings X s) n).obj
          (((SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1}
            (rings X s) n).obj (strictObj k X Q))⟦(-1 : ℤ)⟧)) := by
  let R := SheafOfModules.SequentialDerived.adjacentRestriction (rings X s) n
  have h : Subsingleton (omega k X s (n + 1) ⟶ R.obj ((omega k X s n)⟦(-1 : ℤ)⟧)) := by
    have h0 := intrinsic_restricted_negative_hom k X p hp hchar hk hl
      (quotient s (Nat.le_succ n))
    dsimp only [omega, SheafOfModules.systemLevel,
      SheafOfModules.systemRingHasDerived, Scheme.reductionModulesHasDerivedCategory]
      at h0 ⊢
    simpa only [R, res, SheafOfModules.SequentialDerived.adjacentRestriction,
      SheafOfModules.systemRestriction, rings, Functor.ofOpSequence_obj,
      Functor.ofOpSequence_map_homOfLE_succ,
      SheafOfModules.systemRingHasDerived, Scheme.reductionModulesHasDerivedCategory] using h0
  let := h
  exact (Iso.homCongr (strictLevel k X P (n + 1))
    (R.mapIso ((shiftFunctor _ (-1 : ℤ)).mapIso (strictLevel k X Q n)))).injective.subsingleton

private theorem identification_existsUnique
    (p : ℕ) (hp : p.Prime) (hchar : ringChar k = p)
    (hk : Finite k ∨ IsAlgClosed k) (hl : l ≠ p) {s : Stage l E}
    (P Q : Realization k X s) :
    ∃! i : P.obj ≅ Q.obj, IsIdentification k X P Q i := by
  let d := (SheafOfModules.strictSystemSequenceEquivalence.{u + 1, u, u + 1}
    (rings X s)).mapDerivedCategory
  obtain ⟨i, hi, _hu⟩ :=
    SheafOfModules.SequentialDerived.existsUnique_compatible_iso.{u + 1, u, u + 1}
    (rings X s) (strictObj k X P) (strictObj k X Q)
    (realization_common_lower_bound k X P) (realization_common_lower_bound k X Q)
    (strict_negative_hom k X p hp hchar hk hl P Q)
    (fun n ↦ strictLevel k X P n ≪≫ (strictLevel k X Q n).symm)
    (strict_identification_compatible k X P Q)
  let j : P.obj ≅ Q.obj := d.inverse.preimageIso i
  have hj : d.inverse.map j.hom = i.hom := d.inverse.map_preimage i.hom
  have hjlevel (n : ℕ) : (evaluation X s n).map j.hom ≫ (Q.level n).hom =
      (P.level n).hom := by
    apply (cancel_epi ((evaluationBridge X s n).hom.app P.obj)).1
    rw [← (evaluationBridge X s n).hom.naturality_assoc]
    change (SheafOfModules.derivedSystemEvaluation.{u + 1, u, u + 1}
      (rings X s) n).map (d.inverse.map j.hom) ≫
        (strictLevel k X Q n).hom = (strictLevel k X P n).hom
    rw [hj, hi n]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
  refine ⟨j, hjlevel, ?_⟩
  intro j' hj'
  apply Iso.ext
  apply identification_hom_ext k X P Q
    (realization_common_lower_bound k X P) (realization_common_lower_bound k X Q)
    (strict_negative_hom k X p hp hchar hk hl P Q)
  intro n
  apply (cancel_mono (Q.level n).hom).1
  exact (hj' n).trans (hjlevel n).symm

private theorem scalar_exact {s t : Stage l E} (a : Arrow s t)
    (A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X a))) :
    PreservesFiniteLimits A.model.E ∧ PreservesFiniteColimits A.model.E := by
  apply SheafOfModules.scalarModel_exact_of_sectionwise_flat _ A
  intro U
  let b := levelArrow a U.unop.1
  let := b.ringMap.toAlgebra
  let := (stage_finiteFree b rfl).1
  let := (stage_finiteFree b rfl).2
  obtain ⟨d, β, _hβ⟩ := constantFiniteFree_sectionBasis.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X)
    (CommRingCat.of (atLevel s U.unop.1).ring)
    (CommRingCat.of (atLevel t U.unop.1).ring)
  let V := op U.unop.2
  let R := constantRing X (atLevel s U.unop.1).ring
  let S := constantRing X (atLevel t U.unop.1).ring
  let : Module (R.obj.obj V) (S.obj.obj V) :=
    Module.compHom _ ((constantMap X b.ringMap).hom.app V).hom
  let : Module.Free (R.obj.obj V) (S.obj.obj V) := Module.Free.of_basis (β V)
  change Module.Flat (R.obj.obj V) (S.obj.obj V)
  infer_instance

private theorem scalar_exactDerived {s t : Stage l E} (a : Arrow s t)
    (A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X a)))
    (hlim : PreservesFiniteLimits A.model.E) (hcolim : PreservesFiniteColimits A.model.E) :
    let := hlim
    let := hcolim
    ∃ θ : A.model.T ≅ A.model.E.mapDerivedCategory,
      ∀ K : CochainComplex (SheafOfModules.systemSequenceModules.{u + 1, u, u + 1}
        (rings X s)) ℤ,
        A.model.ε.app K = θ.hom.app (DerivedCategory.Q.obj K) ≫
          A.model.E.mapDerivedCategoryFactors.hom.app K := by
  let := hlim
  let := hcolim
  let := A.model.universal
  let := (A.model.E.exactFunctor_derivedFunctor A.model.E.mapDerivedCategory
    A.model.E.mapDerivedCategoryFactors).2.1
  let θ := Functor.leftDerivedUnique A.model.E.mapDerivedCategory A.model.T
    A.model.ε A.model.E.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso _ (.up ℤ))
  refine ⟨θ, fun K ↦ ?_⟩
  simpa only [θ, Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
    NatTrans.id_app, Iso.refl_hom, Functor.comp_obj, Category.comp_id] using
    (Functor.leftDerivedNatTrans_app A.model.T A.model.E.mapDerivedCategory
      A.model.ε A.model.E.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso _ (.up ℤ)) (𝟙 _) K).symm

private theorem comparison_conjugation {s t : Stage l E} (a : Arrow s t)
    (A : SheafOfModules.SystemScalarModel.{u + 1, u, u + 1}
      (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X a)))
    (P P' : Realization k X s) (Q Q' : Realization k X t)
    (i : P.obj ≅ P'.obj) (j : Q.obj ≅ Q'.obj)
    (hi : IsIdentification k X P P' i) (hj : IsIdentification k X Q Q' j)
    (f : A.model.T.obj P.obj ⟶ Q.obj) (hf : IsComparison k X a A P Q f) :
    IsComparison k X a A P' Q'
      (A.model.T.map i.inv ≫ f ≫ j.hom) := by
  intro n
  have hi' : (evaluation X s n).map i.inv ≫ (P.level n).hom = (P'.level n).hom := by
    rw [← hi n, ← Category.assoc, ← Functor.map_comp, i.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := eq_of_heq (hf n)
  apply heq_of_eq
  rw [A.adjunction.homEquiv_naturality_left, A.adjunction.homEquiv_naturality_right]
  simp only [Functor.map_comp, Category.assoc]
  have hjn := (SheafOfModules.singletonDerivedRestrictionEvaluation.{u + 1, u, u + 1}
    (ringMap X a) n).hom.naturality j.hom
  simp only [Functor.comp_map] at hjn
  rw [reassoc_of% hjn]
  rw [← Functor.map_comp, hj n]
  rw [hn, ← Category.assoc, hi']

end Helpers

attribute [local implicit_reducible] rings atLevel
  Functor.ofOpSequence Functor.ofSequence
  SheafOfModules.systemRingHasDerived
  AlgebraicGeometry.Scheme.reductionModulesHasDerivedCategory

/-- The finite dualizing counit comparisons lift to coherent isomorphisms in the
ordinary unbounded derived category of quotient-semilinear module towers.
Source: current blueprint, `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-finite-extension.proof.md`, paragraphs 3--4 and final paragraph
(blueprint: lem-sf-finite-dualizing-coefficient-tower-map).
Proof: one compactification and its uniform fibre dimension give a common lower
bound for all finite dualizing terms. Sequential realization constructs the specified
counit towers. Constant finite-free section bases make ordinary tower scalar extension
exact; the exact derived-functor uniqueness theorem gives the required comparison.
The normalized comparison lifting lemma gives unique invertible comparisons, and the
full-uniformizer restriction lemma supplies the specified ramification subsequences.
The unit and composite maps are normalized by the finite coherence lemma, so uniqueness
identifies them with the chosen comparisons. Adjacent negative Hom vanishes by scalar
adjunction and the finite foundational negative-self-Hom theorem. Thus the sequential
lifting theorem also gives the unique canonical identifications between realizations.
Conjugation by these identifications preserves normalization, and comparison uniqueness
then gives the replacement equation. -/
theorem finiteDualizingCoefficientTowerMap
    (k : Type u) [Field k] (p : ℕ) (_hp : p.Prime) (_hchar : ringChar k = p)
    (_hk : Finite k ∨ IsAlgClosed k) (l : ℕ) [Fact l.Prime] (_hl : l ≠ p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] :
    Nonempty (ComparisonData (l := l) (E := E) k X) := by
  classical
  let towers (s : Stage l E) : Realization k X s :=
    Classical.choice (realization_exists k X s)
  let scalar {s t : Stage l E} (a : Arrow s t) :=
    Classical.choice (SheafOfModules.nonempty_systemScalarModel
      (SheafOfModules.singletonSequenceRingMap.{u + 1, u, u + 1} (ringMap X a)))
  have hexact {s t : Stage l E} (a : Arrow s t) := scalar_exact X a (scalar a)
  have hcomp {s t : Stage l E} (a : Arrow s t) :=
    normalized_comparison_exists k X p _hp _hchar _hk _hl a
      (scalar a) (towers s) (towers t)
  let f {s t : Stage l E} (a : Arrow s t) := (hcomp a).choose
  have hf {s t : Stage l E} (a : Arrow s t) := (hcomp a).choose_spec
  let comparison {s t : Stage l E} (a : Arrow s t) :
      (scalar a).model.T.obj (towers s).obj ≅ (towers t).obj := by
    let := (hf a).2.1
    exact asIso (f a)
  have hu {s t : Stage l E} (a : Arrow s t) (g) :
      IsComparison k X a (scalar a) (towers s) (towers t) g →
        g = (comparison a).hom := (hf a).2.2 g
  obtain ⟨hunit, hcomposition⟩ := normalized_unit_and_composition (l := l) (E := E)
    k X p _hp _hchar _hk _hl
  refine ⟨{
    towers := towers
    fullUniformizer := fun s ↦ full_uniformizer_restriction k X p _hp _hchar _hk _hl
      s (towers s)
    scalar := scalar
    exact := hexact
    finiteFree := fun a n ↦ stage_finiteFree (levelArrow a n) rfl
    exactDerived := fun a ↦ ⟨(hexact a).1, (hexact a).2,
      scalar_exactDerived X a (scalar a) (hexact a).1 (hexact a).2⟩
    comparison := comparison
    normalized := fun a ↦ (hf a).1
    unique := hu
    unit := ?_
    composition := ?_
    identification := fun _ P Q ↦ identification_existsUnique k X p _hp _hchar _hk _hl P Q
    replacement := ?_ }⟩
  · intro s
    exact (hu (identity s) _ (hunit s (scalar (identity s)) (towers s))).symm
  · intro s t v a b
    have h := hu (composite a b) _
      (hcomposition a b (scalar a) (scalar b) (scalar (composite a b))
        (towers s) (towers t) (towers v) (comparison a).hom (comparison b).hom
        (hf a).1 (hf b).1)
    rw [← h]
    simp only [Iso.hom_inv_id_app_assoc]
  · intro s t a P Q i j hi hj g hg
    have h := hu a _ (comparison_conjugation k X a (scalar a)
      P (towers s) Q (towers t) i j hi hj g hg)
    rw [← h]
    simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.id_comp]

end WeilConjectures.GeneralFieldFiniteDualizingTowers
