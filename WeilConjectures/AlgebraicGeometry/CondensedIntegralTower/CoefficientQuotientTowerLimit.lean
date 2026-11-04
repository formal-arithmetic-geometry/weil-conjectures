/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
public import WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.AlgebraicGeometry.ContinuousRingUniverseRealization
import all WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientCompletionSupplement
import WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Continuous coefficients as limits along uniformizer-power quotient towers

Source: Bhatt--Scholze, Lemma 6.8.2(1) (auxiliary; not a blueprint node).

For a decreasing sequence of ideals `I n` of `𝒪_E`, each of which is a positive power
`ϖ^k 𝒪_E` with `k ≥ n + 1`, the pulled-back continuous integral coefficient ring is the
inverse limit of the pulled-back continuous quotients `𝒪_E / I n`. The ell-power ideals
`ℓ^{n+1} 𝒪_E` form such a sequence (`ell_pow_eq_coefficientExtensionIdeal`).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale.CoefficientQuotientTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The ell-power ideals of `𝒪_E` are uniformizer-power ideals with exponents `r (n + 1)`
for the ramification index `r ≥ 1`.
Source: Serre, Local Fields, Chapter II, §2 (auxiliary; not a blueprint node). -/
theorem ell_pow_eq_coefficientExtensionIdeal :
    ∃ r : ℕ, 1 ≤ r ∧ ∀ n : ℕ,
      Ideal.span ({(l : Padic.coefficientExtensionIntegers l E)} :
          Set (Padic.coefficientExtensionIntegers l E)) ^ (n + 1) =
        Padic.coefficientExtensionIdeal l E (r * (n + 1)) := by
  let R := Padic.coefficientExtensionIntegers l E
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  let : IsLocalRing R := h.2.2.2.1
  let : IsDiscreteValuationRing R := h.2.2.2.2.2.2.2.1
  have hJ : Padic.coefficientExtensionMaximalIdeal l E = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal h.2.2.2.2.1
  have hpi : Ideal.span ({Padic.coefficientExtensionUniformizer l E} : Set R) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hirr : Irreducible (Padic.coefficientExtensionUniformizer l E) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr (hJ.symm.trans hpi.symm)
  have hl : (l : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← hJ]
    apply h.2.1 _ |>.mpr
    change spectralNorm ℚ_[l] E (l : E) < 1
    rw [← map_natCast (algebraMap ℚ_[l] E) l, spectralNorm_extends]
    exact Padic.norm_p_lt_one
  have hl0 : (l : R) ≠ 0 := by
    intro h0
    have h3 : algebraMap ℚ_[l] E l = 0 := by
      rw [map_natCast]
      simpa using congrArg Subtype.val h0
    rw [map_eq_zero_iff _ (algebraMap ℚ_[l] E).injective] at h3
    exact (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero) h3
  obtain ⟨r, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hirr
  refine ⟨r, ?_, fun n ↦ ?_⟩
  · by_contra hr
    obtain rfl : r = 0 := by omega
    rw [pow_zero, mul_one] at hv
    exact (IsLocalRing.mem_maximalIdeal _).mp hl (hv ▸ v.isUnit)
  · rw [hv, Ideal.span_singleton_mul_left_unit v.isUnit, ← Ideal.span_singleton_pow, ← pow_mul,
      Padic.coefficientExtensionIdeal]

variable (I : ℕ → Ideal (Padic.coefficientExtensionIntegers l E))

/-- A quotient by a uniformizer-power ideal is discrete for the quotient topology.
Source: Bhatt--Scholze, Lemma 6.8.2(1) (auxiliary; not a blueprint node). -/
theorem quotient_discreteTopology {J : Ideal (Padic.coefficientExtensionIntegers l E)} {k : ℕ}
    (h : J = Padic.coefficientExtensionIdeal l E k) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    DiscreteTopology (Padic.coefficientExtensionIntegers l E ⧸ J) := by
  subst h
  exact DerivedNakayama.quotientDiscrete l E k

/-- Reductions of a compatible family agree with the coordinates at all lower levels. -/
private theorem mk_eq_of_le (hle : ∀ n, I (n + 1) ≤ I n)
    (t : ∀ n, Padic.coefficientExtensionIntegers l E ⧸ I n)
    (ht : ∀ n, Ideal.Quotient.factor (hle n) (t (n + 1)) = t n) {n m : ℕ} (hnm : n ≤ m)
    (a : Padic.coefficientExtensionIntegers l E) (ha : Ideal.Quotient.mk (I m) a = t m) :
    Ideal.Quotient.mk (I n) a = t n := by
  induction m, hnm using Nat.le_induction with
  | base => exact ha
  | succ m _ ih =>
    apply ih
    rw [← ht m, ← ha, Ideal.Quotient.factor_mk]

/-- Elements of `𝒪_E` are determined by their reductions along a uniformizer-power tower.
Source: Stacks 08ZY (auxiliary; not a blueprint node). -/
theorem eq_of_forall_mk_eq
    (hI : ∀ n, ∃ k, n + 1 ≤ k ∧ I n = Padic.coefficientExtensionIdeal l E k)
    {a b : Padic.coefficientExtensionIntegers l E}
    (h : ∀ n, Ideal.Quotient.mk (I n) a = Ideal.Quotient.mk (I n) b) : a = b := by
  obtain ⟨⟨e, he, -⟩, -⟩ := Padic.coefficientExtension_integers_profinite_tower.{u, u} l E
  apply e.injective
  apply Subtype.ext
  funext m
  rw [he, he]
  obtain ⟨k, hk, hIk⟩ := hI m
  have hsub : I m ≤ Padic.coefficientExtensionIdeal l E (m + 1) :=
    hIk ▸ Ideal.pow_le_pow_right hk
  rw [← Ideal.Quotient.factor_mk hsub, ← Ideal.Quotient.factor_mk hsub, h m]

/-- Compatible continuous maps into a uniformizer-power quotient tower lift uniquely to a
continuous map into `𝒪_E`.
Source: Stacks 08ZY and Bhatt--Scholze, Lemma 6.8.2(1) (auxiliary; not a blueprint node). -/
theorem exists_continuousMap_lift (hle : ∀ n, I (n + 1) ≤ I n)
    (hI : ∀ n, ∃ k, n + 1 ≤ k ∧ I n = Padic.coefficientExtensionIdeal l E k)
    {X : Type*} [TopologicalSpace X]
    (t : ∀ n, letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
      C(X, Padic.coefficientExtensionIntegers l E ⧸ I n))
    (ht : ∀ n x, Ideal.Quotient.factor (hle n) (t (n + 1) x) = t n x) :
    letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    ∃ f : C(X, Padic.coefficientExtensionIntegers l E),
      ∀ n x, Ideal.Quotient.mk (I n) (f x) = t n x := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let : TopologicalSpace (Padic.coefficientExtensionPositiveLimit l E) :=
    Padic.coefficientExtensionPositiveLimitTopology l E
  obtain ⟨⟨e, he, htop⟩, _⟩ := Padic.coefficientExtension_integers_profinite_tower.{u, u} l E
  have heci : Continuous e.symm := by
    have hc : @Continuous _ _ (Padic.coefficientExtensionPositiveLimitTopology l E)
        (Padic.coefficientExtensionIntegersTopology l E) e.symm := by
      let := Padic.coefficientExtensionIntegersTopology l E
      exact (e.toEquiv.toHomeomorphOfContinuousOpen htop.continuous
        htop.isOpenMap).symm.continuous
    rw [← Scheme.coefficientIntegersTopology_eq l E] at hc
    exact hc
  choose k hk hIk using hI
  have hsub (m : ℕ) : I m ≤ Padic.coefficientExtensionIdeal l E (m + 1) :=
    hIk m ▸ Ideal.pow_le_pow_right (hk m)
  let s (m : ℕ) (x : X) : Padic.coefficientExtensionRing l E (m + 1) :=
    Ideal.Quotient.factor (hsub m) (t m x)
  let b (x : X) : Padic.coefficientExtensionPositiveLimit l E :=
    ⟨fun m ↦ s m x, by
      apply Subring.mem_iInf.mpr
      intro m
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (t (m + 1) x)
      have ha' := mk_eq_of_le l E I hle (fun n ↦ t n x) (fun n ↦ ht n x) m.le_succ a ha
      simp only [RingHom.mem_eqLocus, RingHom.comp_apply, Pi.evalRingHom_apply, s, ← ha, ← ha',
        Ideal.Quotient.factor_mk,
        Padic.coefficientExtensionTransition]⟩
  have hb : Continuous b := by
    apply (continuous_induced_rng
      (f := fun x : Padic.coefficientExtensionPositiveLimit l E ↦ x.val)
      (g := b) (t₂ := @Pi.topologicalSpace ℕ
        (fun n ↦ Padic.coefficientExtensionRing l E (n + 1)) (fun _ ↦ ⊥))).mpr
    apply (continuous_pi (T := fun _ ↦ ⊥))
    intro m
    have := quotient_discreteTopology l E (hIk m)
    have hc : @Continuous _ (Padic.coefficientExtensionRing l E (m + 1)) _ ⊥
        (Ideal.Quotient.factor (hsub m)) :=
      @continuous_of_discreteTopology _ _ _ _ ⊥ _
    exact @Continuous.comp _ _ _ _ _ ⊥ _ _ hc (t m).continuous
  refine ⟨⟨fun x ↦ e.symm (b x), heci.comp hb⟩, fun n x ↦ ?_⟩
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (t (k n - 1) x)
  have hm : k n - 1 + 1 = k n := by
    have := hk n
    omega
  have h1 : Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (k n - 1 + 1))
      (e.symm (b x)) = Ideal.Quotient.mk _ a := by
    rw [← he, e.apply_symm_apply, ← Ideal.Quotient.factor_mk (hsub (k n - 1)), ha]
  rw [Ideal.Quotient.eq, hm, ← hIk n, ← Ideal.Quotient.eq] at h1
  have hnm : n ≤ k n - 1 := by
    have := hk n
    omega
  exact h1.trans (mk_eq_of_le l E I hle (fun n ↦ t n x) (fun n ↦ ht n x) hnm a ha)

section Sheaves

variable (X : Scheme.{u})

/-- The abelian pro-etale sheaf of continuous maps into a topological ring. -/
private abbrev continuousAb (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] :=
  (sheafCompose (Scheme.ProEt.topology X) (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (continuousCoefficientRingSheaf X A)

/-- Postcomposition with a continuous ring homomorphism. -/
private def continuousMap {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) : continuousAb X A ⟶ continuousAb X B :=
  ⟨{ app := fun _ ↦ AddCommGrpCat.ofHom
      (ULift.ringEquiv.symm.toAddEquiv.toAddMonoidHom.comp
        ((f.compLeftContinuous _ hf).toAddMonoidHom.comp ULift.ringEquiv.toAddEquiv.toAddMonoidHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The continuous-ring realization comparison is natural in the coefficient ring. -/
private theorem realization_natural {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    (f : A →+* B) (hf : Continuous f) :
    (upperStarFromPoint X).map
      ((sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
          (show Profinite.continuousMapRingSheafOfUniverse A ⟶
            Profinite.continuousMapRingSheafOfUniverse B from
            ⟨{ app := fun _ ↦ RingCat.ofHom
                (ULift.ringEquiv.symm.toRingHom.comp
                  ((f.compLeftContinuous _ hf).comp ULift.ringEquiv.toRingHom))
               naturality := fun _ _ _ ↦ rfl }⟩)) ≫
        ContinuousRingUniverse.comparison X B =
      ContinuousRingUniverse.comparison X A ≫ continuousMap X f hf := by
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ X))
  apply (adj.homEquiv _ _).injective
  dsimp only [upperStarFromPoint]
  rw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_right]
  simp only [ContinuousRingUniverse.comparison]
  change _ ≫ adj.homEquiv _ _ (adj.homEquiv _ _ |>.symm _) =
    adj.homEquiv _ _ (adj.homEquiv _ _ |>.symm _) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext S x
  rfl

variable (hle : ∀ n, I (n + 1) ≤ I n)

/-- The continuous quotient tower on the pro-etale site. -/
private def continuousSequence : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  Functor.ofOpSequence (X := fun n ↦ continuousAb X (Padic.coefficientExtensionIntegers l E ⧸ I n))
    (fun n ↦ continuousMap X (Ideal.Quotient.factor (hle n))
      (continuous_quot_lift _ continuous_quot_mk))

/-- The continuous quotient cone on the pro-etale site. -/
private def continuousCone : Cone (continuousSequence l E I X hle) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  refine ⟨continuousAb X (Padic.coefficientExtensionIntegers l E),
    NatTrans.ofOpSequence (fun n ↦ continuousMap X (Ideal.Quotient.mk (I n))
      continuous_quot_mk) ?_⟩
  intro n
  dsimp only [continuousSequence]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  ext U f
  rfl

private theorem continuousCone_isLimit
    (hI : ∀ n, ∃ k, n + 1 ≤ k ∧ I n = Padic.coefficientExtensionIdeal l E k) :
    Nonempty (IsLimit (continuousCone l E I X hle)) := by
  classical
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  refine ⟨isLimitOfReflects (sheafToPresheaf (Scheme.ProEt.topology X) Ab.{u + 1}) ?_⟩
  apply evaluationJointlyReflectsLimits
  intro U
  apply isLimitOfReflects (forget Ab.{u + 1})
  apply Classical.choice
  apply (Types.isLimit_iff_bijective_sectionOfCone _).mpr
  constructor
  · intro f g hfg
    apply ULift.ext
    apply ContinuousMap.ext
    intro x
    apply eq_of_forall_mk_eq l E I hI
    intro n
    exact congrArg (fun s ↦ (s.val (op n)).down x) hfg
  · intro s
    let t (n : ℕ) : C(U.unop.left, Padic.coefficientExtensionIntegers l E ⧸ I n) :=
      (s.val (op n)).down
    have ht (n : ℕ) (x : U.unop.left) :
        Ideal.Quotient.factor (hle n) (t (n + 1) x) = t n x := by
      have hn := s.property (homOfLE n.le_succ).op
      simp only [Functor.comp_map, continuousSequence,
        Functor.ofOpSequence_map_homOfLE_succ] at hn
      exact congrArg (fun f ↦ f.down x) hn
    obtain ⟨f, hf⟩ := exists_continuousMap_lift l E I hle hI t ht
    refine ⟨ULift.up f, ?_⟩
    apply Subtype.ext
    funext n
    apply ULift.ext
    apply ContinuousMap.ext
    exact hf n.unop

/-- The continuous condensed quotient ring `𝒪_E / J` on the point. -/
abbrev pointQuotientRing (J : Ideal (Padic.coefficientExtensionIntegers l E)) :
    Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1} :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
    (Profinite.continuousCoefficientRingSheaf (Padic.coefficientExtensionIntegers l E ⧸ J))

/-- Continuous postcomposition with the quotient map `𝒪_E → 𝒪_E / J`, on the point. -/
def pointQuotientMap (J : Ideal (Padic.coefficientExtensionIntegers l E)) :
    DerivedNakayama.integerRing l E ⟶ pointQuotientRing l E J :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ⟨{ app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            (((Ideal.Quotient.mk J).compLeftContinuous _ continuous_quot_mk).comp
              ULift.ringEquiv.toRingHom))
       naturality := fun _ _ _ ↦ rfl }⟩

/-- Continuous postcomposition with the factor map `𝒪_E / J → 𝒪_E / K`, on the point. -/
def pointFactorMap {J K : Ideal (Padic.coefficientExtensionIntegers l E)} (h : J ≤ K) :
    pointQuotientRing l E J ⟶ pointQuotientRing l E K :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ⟨{ app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            (((Ideal.Quotient.factor h).compLeftContinuous _
              (continuous_quot_lift _ continuous_quot_mk)).comp ULift.ringEquiv.toRingHom))
       naturality := fun _ _ _ ↦ rfl }⟩

/-- Quotient maps compose with factor maps. -/
@[reassoc (attr := simp)]
theorem pointQuotientMap_comp_pointFactorMap
    {J K : Ideal (Padic.coefficientExtensionIntegers l E)} (h : J ≤ K) :
    pointQuotientMap l E J ≫ pointFactorMap l E h = pointQuotientMap l E K := by
  ext U f
  rfl

/-- The pulled-back quotient tower of a decreasing sequence of ideals. -/
def pullbackSequence : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology X) Ab.{u + 1} :=
  Functor.ofOpSequence (X := fun n ↦ (upperStarFromPoint X).obj (pointQuotientRing l E (I n)))
    (fun n ↦ (upperStarFromPoint X).map (pointFactorMap l E (hle n)))

/-- The pulled-back quotient cone of a decreasing sequence of ideals. -/
def pullbackCone : Cone (pullbackSequence l E I X hle) :=
  ⟨(upperStarFromPoint X).obj (DerivedNakayama.integerRing l E),
    NatTrans.ofOpSequence (fun n ↦ (upperStarFromPoint X).map (pointQuotientMap l E (I n)))
      (fun n ↦ by
        simp only [Functor.const_obj_map, pullbackSequence,
          Functor.ofOpSequence_map_homOfLE_succ, ← Functor.map_comp,
          pointQuotientMap_comp_pointFactorMap]
        exact Category.id_comp _)⟩

/-- The realization comparisons identify the pulled-back tower with the continuous tower. -/
private def realizationTower
    (hI : ∀ n, ∃ k, n + 1 ≤ k ∧ I n = Padic.coefficientExtensionIdeal l E k) :
    pullbackSequence l E I X hle ≅ continuousSequence l E I X hle := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let e (n : ℕ) := ContinuousRingUniverse.comparison X
    (Padic.coefficientExtensionIntegers l E ⧸ I n)
  have he (n : ℕ) : IsIso (e n) := by
    obtain ⟨k, -, hk⟩ := hI n
    have := quotient_discreteTopology l E hk
    have : TotallySeparatedSpace (Padic.coefficientExtensionIntegers l E ⧸ I n) :=
      TotallySeparatedSpace.of_discrete _
    have : TotallyDisconnectedSpace (Padic.coefficientExtensionIntegers l E ⧸ I n) :=
      TotallySeparatedSpace.totallyDisconnectedSpace _
    exact ContinuousRingUniverse.comparison_isIso X _
  let t : pullbackSequence l E I X hle ⟶ continuousSequence l E I X hle :=
    NatTrans.ofOpSequence e (by
      intro n
      dsimp only [pullbackSequence, continuousSequence]
      rw [Functor.ofOpSequence_map_homOfLE_succ, Functor.ofOpSequence_map_homOfLE_succ]
      exact realization_natural X (Ideal.Quotient.factor (hle n))
        (continuous_quot_lift _ continuous_quot_mk))
  have (n : ℕᵒᵖ) : IsIso (t.app n) := he n.unop
  exact NatIso.ofComponents (fun n ↦ asIso (t.app n)) (fun f ↦ t.naturality f)

/-- The pulled-back continuous integral coefficient ring is the limit of its pulled-back
quotients along any decreasing sequence of positive uniformizer-power ideals.
Source: Bhatt--Scholze, Lemma 6.8.2(1) (auxiliary; not a blueprint node). -/
theorem pullbackCone_isLimit
    (hI : ∀ n, ∃ k, n + 1 ≤ k ∧ I n = Padic.coefficientExtensionIdeal l E k) :
    Nonempty (IsLimit (pullbackCone l E I X hle)) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have : TotallyDisconnectedSpace (Padic.coefficientExtensionIntegers l E) := by
    have h := (Padic.coefficientExtension_integers_profinite_tower.{u, u} l E).2.2.2.1
    rw [← Scheme.coefficientIntegersTopology_eq l E] at h
    exact h
  have : IsIso (ContinuousRingUniverse.comparison X
      (Padic.coefficientExtensionIntegers l E)) :=
    ContinuousRingUniverse.comparison_isIso X _
  let e := asIso (ContinuousRingUniverse.comparison X
    (Padic.coefficientExtensionIntegers l E))
  let c := pullbackCone l E I X hle
  have hc : IsLimit ((Cone.postcompose (realizationTower l E I X hle hI).hom).obj c) := by
    apply IsLimit.ofIsoLimit (continuousCone_isLimit l E I X hle hI).some
    refine Cone.ext e.symm ?_
    intro n
    apply (cancel_epi e.hom).mp
    rw [Iso.symm_hom, Iso.hom_inv_id_assoc]
    exact (realization_natural X (Ideal.Quotient.mk (I n.unop)) continuous_quot_mk).symm
  exact ⟨(IsLimit.postcomposeHomEquiv (realizationTower l E I X hle hI) c) hc⟩

end Sheaves

end AlgebraicGeometry.ProEtale.CoefficientQuotientTower
