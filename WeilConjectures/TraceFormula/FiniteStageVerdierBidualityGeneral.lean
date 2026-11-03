/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.FiniteStageVerdierBiduality
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteStageVerdierBiduality
import all WeilConjectures.SixFunctors.Etale.EtaleGeometricBiduality
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteDualitySiteComparison
import WeilConjectures.AlgebraicGeometry.BidualityFieldExtension
import WeilConjectures.SixFunctors.Etale.Derived.Stalks.Basic
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategorySymmetric
import Mathlib.FieldTheory.IsSepClosed

/-!
# Finite-stage Verdier biduality over finite or algebraically closed fields

Source: latest blueprint,
part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/
sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-fix-general-biduality.md and its proof, with the field-scope correction of
Wei Yang, Zulip #1441, item 28 (blueprint: thm-fix-general-biduality).

The existing conclusion predicates retain both specified ambient dual functors,
the intrinsic finite-Tor constructible subcategories and the canonical evaluation
transposes. Neither a Frobenius datum nor a boundary-duality assumption is needed.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale

private theorem generalSiteHom
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X : Scheme.{u}} [IsNoetherian X]
    [HasInvertibleExponent Λ X]
    (K M : Etale.DerivedCategoryModule Λ X)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) X K)
    (hM : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) X M) :
    IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X K M) := by
  let : (comparisonUpperStar (ModuleCat.{u + 1} Λ) X).PreservesFlat :=
    preservesFlat_comparisonUpperStar (X := X)
  let P := siteHomComparisonLocus Λ X M
  have ht := siteHomComparison_exact_thick Λ X M
  unfold siteHomSiteExactThick siteHomExactThickAssertion at ht
  obtain ⟨sB, sE, β, hβ, _, htri, hret⟩ := ht
  have : P.IsTriangulated := htri
  have : P.IsStableUnderRetracts := hret
  have : P.IsClosedUnderIsomorphisms := by
    refine ⟨fun {B C} e hB ↦ ?_⟩
    change IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X B M) at hB
    have : IsIso (β.app (op B)) := by simpa only [hβ] using hB
    have : IsIso (β.app (op C)) := NatTrans.isIso_app_of_iso β e.op
    change IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} Λ) X C M)
    simpa only [hβ] using (inferInstance : IsIso (β.app (op C)))
  apply etaleThickGeneration X Λ P ?_ K
    ((WeilConjectures.boundedConstructible_iff_source Λ X K).mpr hK.1) ?_
  · rintro B ⟨str, i, j, hj, L, hji, hL, hf, ⟨e⟩⟩
    let := hj
    let := hL
    have hs : IsImmersion (str.immersion i) := str.isImmersion i
    let := hs
    have : TopologicalSpace.NoetherianSpace (str.domain i) :=
      (str.immersion i).isEmbedding.isInducing.noetherianSpace
    let c := (str.immersion i).liftCoborder
    let v := (str.immersion i).coborderRange.ι
    have hcv : c ≫ v = str.immersion i := (str.immersion i).liftCoborder_ι
    have : QuasiCompact (c ≫ v) := by rw [hcv]; infer_instance
    have hb := isIso_stratumHom Λ c v L hf
      ⟨M, (WeilConjectures.boundedConstructible_iff_source Λ X M).mpr hM⟩
    have hj' : j = (str.immersion i).toImage := by
      apply (cancel_mono (str.immersion i).imageι).mp
      exact hji.trans (Scheme.Hom.toImage_imageι _).symm
    subst j
    obtain ⟨_, he, _⟩ :=
      (etale_locallyClosed_extension_comparison (A := Λ) X (𝟙 X) v).2
        (str.immersion i)
    obtain ⟨es, _, _⟩ := he c v hcv
    have e' : (DerivedCategory.singleFunctor _ 0).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} Λ) (str.immersion i).imageι).obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
            (str.immersion i).toImage).obj L)) ≅
        (locallyClosedEtaleExtension Λ c v).obj
          ((DerivedCategory.singleFunctor _ 0).obj L) := by
      let Q := Etale.lowerStar (ModuleCat.{u + 1} Λ) c ⋙
        Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) v
      have ee : (Etale.lowerStar (ModuleCat.{u + 1} Λ) (str.immersion i).imageι).obj
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ)
            (str.immersion i).toImage).obj L) ≅ Q.obj L := by
        exact es.app L
      exact (DerivedCategory.singleFunctor _ 0).mapIso ee ≪≫
        ((Q.mapDerivedCategorySingleFunctor 0).app L).symm ≪≫
        (Functor.mapDerivedCategoryCompIso
          (Etale.lowerStar (ModuleCat.{u + 1} Λ) c)
          (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} Λ) v)).app _ ≪≫
        (StratumHomComparisonMate.Etale.extensionIso Λ c v).symm.app _
    exact P.prop_of_iso (e ≪≫ e').symm hb
  · obtain ⟨a, b, ht⟩ := hK.2
    refine ⟨min a b, b, min_le_right _ _, ?_⟩
    exact Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.mpr
      (Etale.DerivedCategory.torAmplitudeIn.mono (min_le_left _ _) le_rfl ht)


end AlgebraicGeometry.ProEtale

namespace WeilConjectures


private theorem coefficientKilled
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
  have h := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := Padic l) (L := E))).choose_spec.choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Padic.coefficientExtensionIdeal l E n := by
    change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  have hkill : ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
    change ((l ^ n : ℕ) :
      Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
      Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Nat.cast_pow] using hpow
  exact hkill

private theorem coefficientExponent
    (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] (hl : ringChar k ≠ l)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) :
    HasInvertibleExponent (ULift.{u + 1, u} (Padic.coefficientExtensionRing l E n))
      (Spec (.of k)) := by
  have hell : (l : k) ≠ 0 := fun h ↦
    hl (CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) h)
  refine ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, ?_, ?_⟩
  · exact ULift.down_injective (coefficientKilled l E n)
  · have hu : IsUnit ((l ^ n : ℕ) : k) := by
      simpa only [Nat.cast_pow] using hell.isUnit.pow n
    simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom

section PairingNormalization

attribute [local instance] _root_.DerivedCategory.symmetricCategory'

/-- The normalized pairing evaluation is native evaluation after Koszul symmetry.
Apply the inverse tensor-Hom adjunction to its identity-adjunct equation and cancel
its prescribed symmetry. Source: lem-weil-duality-pairing, evaluation clause;
thm-fix-general-biduality proof step 3 (blueprint: thm-fix-general-biduality). -/
private theorem etalePairingEvaluation_eq
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u})
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (p : Etale.AmbientDualityPairing B X W)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    Etale.fieldExtensionEvaluation B X p K =
      (β_ (((Etale.derivedHom B X).obj (op K)).obj W) K).hom ≫
        (ihom.ev K).app W := by
  let DK := ((Etale.derivedHom B X).obj (op K)).obj W
  have hb : ((p.choose.hom.app K).app DK) = (β_ K DK).hom :=
    eq_of_heq (p.choose_spec.1 K DK)
  have he := congrArg ((Etale.derivedTensorHomAdjunction B K).homEquiv DK W).symm
    (p.choose_spec.2.choose_spec.1 K)
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_id] at he
  change ((p.choose.hom.app K).app DK) ≫ Etale.fieldExtensionEvaluation B X p K =
    (ihom.ev K).app W at he
  rw [hb] at he
  apply (cancel_epi ((β_ K DK).hom)).mp
  rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  exact he

/-- The pairing's transpose equation fixes its double-dual map to the native map.
Substitute the evaluation normalization into that equation.
Source: lem-weil-duality-pairing, transpose clause;
thm-fix-general-biduality proof step 3 (blueprint: thm-fix-general-biduality). -/
private theorem etalePairingBiduality_eq
    (B : Type v) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u})
    {W : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)}
    (p : Etale.AmbientDualityPairing B X W)
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    Etale.AmbientDualityPairing.bidualityMap B X p K =
      MonoidalClosed.toIhomIhom W K := by
  change p.choose_spec.2.choose_spec.2.choose K = _
  calc
    p.choose_spec.2.choose_spec.2.choose K =
        (Etale.derivedTensorHomAdjunction B
          (((Etale.derivedHom B X).obj (op K)).obj W)).homEquiv K W
          (Etale.fieldExtensionEvaluation B X p K) :=
      p.choose_spec.2.choose_spec.2.choose_spec.1 K
    _ = _ := by
      change MonoidalClosed.curry (Etale.fieldExtensionEvaluation B X p K) = _
      rw [etalePairingEvaluation_eq]
      rfl

end PairingNormalization

private theorem finiteFieldDelta
    (ell : ℕ) [Fact ell.Prime]
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, (ell : A) ^ r = 0)
    {k : Type u} [Field k] [Finite k] [Fact (ringChar k ≠ ell)]
    [HasInvertibleExponent A (Spec (.of k))]
    {X : Scheme.{u}} (a : X ⟶ Spec (.of k))
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (K : Etale.DerivedCategoryModule A X)
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} A) X K) :
    IsIso ((Etale.verdierDualDoubleDual A a).app K) := by
  let : IsAlgClosed (SeparableClosure k) :=
    IsAlgClosure.isAlgClosed (R := k) (K := SeparableClosure k)
  let b := Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k)))
  let X' := pullback a b
  let g : X' ⟶ X := pullback.fst a b
  let a' : X' ⟶ Spec (.of (SeparableClosure k)) := pullback.snd a b
  let sq : IsPullback g a' a b := IsPullback.of_hasPullback a b
  let : IsSeparated a' := MorphismProperty.of_isPullback sq inferInstance
  let : LocallyOfFiniteType a' := MorphismProperty.of_isPullback sq inferInstance
  let : QuasiCompact a' := MorphismProperty.of_isPullback sq inferInstance
  let : HasInvertibleExponent A (Spec (.of (SeparableClosure k))) := .of_hom b
  let : HasCompactification a := (NagataCompactification a).hasCompactification
  let : HasCompactification a' := (NagataCompactification a').hasCompactification
  have hc := Etale.det_pd_biduality_field_extension ell hA
    (k' := SeparableClosure k) a K K hK hK
  have h₁ : IsIso (Etale.fieldExtensionDualComparison A g a a' b sq K) :=
    hc.dualComparison
  have h₂ : IsIso (Etale.fieldExtensionDualComparison A g a a' b sq
      ((Etale.verdierDual A a).obj (op K))) := hc.iteratedDualComparison
  have hd := hc.doubleDual
  simp only [etalePairingBiduality_eq,
    ← Etale.verdierDualDoubleDual_app] at hd
  have hup := Etale.isIso_verdierDualDoubleDual_app A a'
    (Etale.constructibleFiniteTor_leftDerivedUpperStar (ModuleCat.{u + 1} A) g hK)
  have hh : IsIso ((L(Etale.upperStar (ModuleCat.{u + 1} A) g)).map
      ((Etale.verdierDualDoubleDual A a).app K) ≫
        Etale.fieldExtensionDualComparison A g a a' b sq
          ((Etale.verdierDual A a).obj (op K))) := by
    rw [hd]
    infer_instance
  have hm : IsIso ((L(Etale.upperStar (ModuleCat.{u + 1} A) g)).map
      ((Etale.verdierDualDoubleDual A a).app K)) :=
    IsIso.of_isIso_comp_right _
      (Etale.fieldExtensionDualComparison A g a a' b sq
        ((Etale.verdierDual A a).obj (op K)))
  exact (Etale.isIso_iff_isIso_leftDerivedUpperStar_sepClosureBaseChange_map A a _).2 hm

/-- Verdier duality at every positive coefficient level is an exact anti-equivalence
on bounded constructible finite-Tor complexes on each small site, and its canonical
evaluation transpose is invertible. The two predicates are the published etale and
intrinsic pro-etale conclusions, with their actual restricted functors and maps.

Source: latest blueprint,
part-duality-trace-formula/sec-smooth-purity/sec-sp-grp-ladic-summary/
sec-towers-and-integral-coefficients/sk-lem-sp-tower/
thm-fix-general-biduality.md and its proof; Wei Yang #1441, item 28
(blueprint: thm-fix-general-biduality).

Proof:
1. Independent preservation (lem-weil-verdier-preservation-strata) puts DK and the
   dualizing object in Dctf. For algebraically closed k apply
   thm-weil-etale-geometric-biduality, in its arbitrary-field formulation.
2. For finite k, pull back to its separable algebraic closure. First form compact-support
   exchange alpha using lem-amb-unbounded-compact-support-comparisons. Define the
   dualizing map w as the adjunct of the pulled-back exceptional counit composed with
   alpha inverse. Thus epsilon upstairs after R a_!(w) after alpha is the pulled-back
   epsilon. BEFORE descending biduality, det-pd-biduality-field-extension proves that
   this w, closed exceptional restriction and the evaluation-defined Hom comparisons
   are invertible. In particular c_K is Hom(1,w) after the pulled-back evaluation
   transpose beta_(K,omega), and the same holds at DK by independent preservation.
3. Braided derived pullback and lem-pur-lax-symmetric-bidual-square identify the actual
   double-dual arrows: delta_(g*K) = D'(c_K inverse) after c_DK after g*(delta_K).
   Geometric biduality upstairs and lem-kun-sep-closure-conservative therefore imply
   invertibility of delta_K downstairs. Native internal Hom is contravariantly exact
   by lem-weil-native-internal-hom-contravariant-exact. Naturality and the evaluation
   triangle identity D(delta_K) after delta_DK = identity give the anti-equivalence
   with quasi-inverse D, retaining the pairing of lem-weil-duality-pairing.
4. Every intrinsic bounded constructible pro-etale object has an etale representative
   by lem-sf-proetale-constructible-origin. It is bounded below, so
   lem-exc-comparison-tor-interval preserves and reflects its Tor interval. Hence nu*
   is an equivalence on Dctf. Apply lem-weil-finite-duality-site-comparison to
   (K,omega) and (DK,omega). Its specified dualizing and evaluation-compatible Hom
   comparisons transport the exact anti-equivalence and the actual double-dual maps.
   The pro-etale dualizing object is the comparison transport nu* a^times Rnu_* A;
   no ambient pro-etale exceptional adjoint is assumed.
-/
theorem finite_stage_verdier_biduality_general
    (l : ℕ) [Fact l.Prime] {k : Type u} [Field k]
    (_hk : Finite k ∨ IsAlgClosed k) (_hl : ringChar k ≠ l)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of k))
    [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] :
    FiniteEtaleGeometricBiduality l E n hn Y aY ∧
      FiniteProEtaleVerdierBiduality l E n hn Y aY := by
  classical
  let A := Padic.coefficientExtensionRing l E n
  have : Finite A := Padic.finite_coefficientExtensionRing l E n hn
  let Λ := ULift.{u + 1, u} A
  have : Fact (ringChar k ≠ l) := ⟨_hl⟩
  have : PerfectField k := by
    rcases _hk with h | h
    · let := h
      infer_instance
    · let := h
      infer_instance
  have : HasInvertibleExponent Λ (Spec (.of k)) := coefficientExponent l _hl E n
  have : HasInvertibleExponent Λ Y := .of_hom aY
  have : HasCompactification aY := (NagataCompactification aY).hasCompactification
  have hδ (K : Etale.DerivedCategoryModule Λ Y)
      (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y K) :
      IsIso ((Etale.verdierDualDoubleDual Λ aY).app K) := by
    rcases _hk with hk | hk
    · let := hk
      apply finiteFieldDelta l Λ ?_ aY K hK
      refine ⟨n, ?_⟩
      apply ULift.down_injective
      change (l : Padic.coefficientExtensionRing l E n) ^ n = 0
      simpa only [Nat.cast_pow] using coefficientKilled l E n
    · let := hk
      exact Etale.isIso_verdierDualDoubleDual_app Λ aY hK
  let P := finiteTorConstructibleEtale l E n hn Y
  let Q := Etale.DerivedCategory.isBoundedConstructible Λ Y
  let P' := finiteTorConstructibleProEtaleModule l E n hn Y
  have hP := finiteTorConstructibleEtale_iff_source l E n hn Y
  have hD (K) (hK : P K) : P ((Etale.verdierDual Λ aY).obj (op K)) :=
    (hP _).mpr (Etale.constructibleFiniteTor_verdierDual Λ aY ((hP K).mp hK))
  have hEt : FiniteEtaleGeometricBiduality l E n hn Y aY :=
    ⟨(Etale.ambient_duality_pairing Λ aY).1,
      geometric_biduality_conclusion P _ _ (fun K hK ↦ hδ K ((hP K).mp hK)) hD
        (verdierDual_exact Λ aY)⟩
  refine ⟨hEt, ?_⟩
  have : IsNoetherian Y := {
    __ := LocallyOfFiniteType.isLocallyNoetherian aY
    __ := QuasiCompact.compactSpace_of_compactSpace aY }
  have : (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) Y).PreservesFlat :=
    ProEtale.preservesFlat_comparisonUpperStar (X := Y)
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h ↦
    (hP _).mpr ((Etale.DerivedCategory.constructibleFiniteTor _ Y).prop_of_iso e
      ((hP _).mp h))⟩
  have hP' : ∀ {K L}, (K ≅ L) → P' K → P' L := fun e h ↦
    (finiteTor_proEtale_iff l E n hn Y _).mpr
      ((ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).prop_of_iso
        e ((finiteTor_proEtale_iff l E n hn Y _).mp h))
  have : P'.IsClosedUnderIsomorphisms := ⟨hP'⟩
  obtain ⟨e, ⟨he⟩⟩ := finiteTor_comparison_equivalence l E n hn Y
  let c := NagataCompactification aY
  have hc := ProEtale.comparisonData_of_verdier Λ aY
    (ProEtale.finiteDualityProEtaleObject A c) (ProEtale.finiteDualityObjectMap A c)
    (ProEtale.isIso_objectMap A c) P Q P'
    (fun K M hK hM ↦ ProEtale.generalSiteHom Λ K M ((hP K).mp hK)
      ((boundedConstructible_iff_source Λ Y M).mp hM))
    ((boundedConstructible_iff_source Λ Y _).mpr
      (ProEtale.dualizing_boundedConstructible Λ aY))
    hD (fun K hK ↦ hδ K ((hP K).mp hK)) hEt.1
    ((Etale.ambient_duality_pairing Λ aY).2 _) e he
  exact fixedProEtaleConclusion A c P Q P' hP' hc

end WeilConjectures
