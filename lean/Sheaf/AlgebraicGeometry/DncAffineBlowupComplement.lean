/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import WeilConjectures.Blowup.Affine.ChartAlgebra
public import WeilConjectures.Compactification.StrictTransform
public import WeilConjectures.Compactification.StrictTransformChartModel
import WeilConjectures.Blowup.FiniteDegree.Algebra

/-!
# The affine deformation chart as a strict-transform complement

Source: Stacks Project, divisors.tex, Tags 0804 and 080D, specialized to the centre
`(I,t)` in `Spec R[t]` (blueprint: lem-pur-dnc-affine-blowup-complement).

The auxiliary definitions specialize the existing ideal and strict-transform constructions;
the charts are the recorded `AffineBlowup.chartRingιOfEq`. No new model for any of these
constructions is introduced.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.DncAffineBlowup

variable {R : Type u} [CommRing R]

/-- The centre ideal `(I,t)` in `R[t]`. Source: Stacks, Tag 0804, affine specialization
(blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def centerIdeal (I : Ideal R) : Ideal (Polynomial R) :=
  I.map Polynomial.C ⊔ Ideal.span {Polynomial.X}

/-- The distinguished generator `t` of the centre. Source: Stacks, Tag 0804
(blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def parameter (I : Ideal R) : centerIdeal I :=
  ⟨Polynomial.X, Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))⟩

/-- A constant generator of the centre. Source: Stacks, Tag 0804
(blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def constant (I : Ideal R) (a : I) : centerIdeal I :=
  ⟨Polynomial.C (a : R), Ideal.mem_sup_left (Ideal.mem_map_of_mem Polynomial.C a.2)⟩

/-- The ideal sheaf of the centre on the affine spectrum. Source: Stacks, Tag 0804
(blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def center (I : Ideal R) : (Spec (.of (Polynomial R))).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop
    ((centerIdeal I).map (Scheme.ΓSpecIso (.of (Polynomial R))).inv.hom)

/-- The closed immersion `V(t) → Spec R[t]`. Source: Stacks, Tag 080D
(blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def hyperplane (R : Type u) [CommRing R] :
    Spec (.of (Polynomial R ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial R)))) ⟶
      Spec (.of (Polynomial R)) :=
  Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.span {Polynomial.X} : Ideal (Polynomial R))))

/-- The ideal sheaf of the scheme-theoretic strict transform, viewed inside the blow-up.
Source: Stacks, Tag 080D (blueprint: lem-pur-dnc-affine-blowup-complement). -/
noncomputable def transformIdeal (I : Ideal R) : (center I).blowup.IdealSheafData :=
  (strictTransformMap (hyperplane R) (center I).blowupMap (center I).support.compl).ker

private lemma exists_affineEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (K : Ideal A) (L : Ideal B) (h : K.map e.toRingHom = L) :
    ∃ e' : AffineBlowup K ≅ AffineBlowup L,
      e'.hom ≫ AffineBlowup.toSpec L =
        AffineBlowup.toSpec K ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom) := by
  have h' : L.map e.symm.toRingHom = K := by
    rw [← h, Ideal.map_map]
    convert Ideal.map_id K using 1
    ext x
    simp
  let e' : AffineBlowup K ≅ AffineBlowup L :=
    { hom := AffineBlowup.hom e.symm.toRingHom h'
      inv := AffineBlowup.hom e.toRingHom h
      hom_inv_id := by
        rw [← AffineBlowup.hom_comp]
        exact (AffineBlowup.hom_congr (by ext x; simp) _).trans AffineBlowup.hom_id
      inv_hom_id := by
        rw [← AffineBlowup.hom_comp]
        exact (AffineBlowup.hom_congr (by ext x; simp) _).trans AffineBlowup.hom_id }
  exact ⟨e', AffineBlowup.hom_toSpec _ _⟩

private lemma exists_comparison {A : Type u} [CommRing A] (K : Ideal A)
    (J : (Spec (.of A)).IdealSheafData)
    (hJ : J.ideal ⟨⊤, isAffineOpen_top _⟩ =
      K.map (Scheme.ΓSpecIso (.of A)).inv.hom) :
    ∃ e : AffineBlowup K ≅ J.blowup,
      e.hom ≫ J.blowupMap = AffineBlowup.toSpec K := by
  let X := Spec (.of A)
  let U : X.affineOpens := ⟨⊤, isAffineOpen_top X⟩
  let e := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  have hι : IsIso (J.blowupι U) :=
    (J.isPullback_blowupι U).isIso_snd_of_isIso (X.topIso.isIso_hom)
  obtain ⟨e', he'⟩ := exists_affineEquiv e K (J.ideal U) hJ.symm
  refine ⟨e' ≪≫ asIso (J.blowupι U), ?_⟩
  change e'.hom ≫ J.blowupι U ≫ J.blowupMap = _
  rw [J.blowupι_comp_blowupMap, IsAffineOpen.fromSpec_top,
    Scheme.isoSpec_Spec_inv, ← Category.assoc, he', Category.assoc, ← Spec.map_comp]
  have hid : (Scheme.ΓSpecIso (.of A)).inv ≫
      CommRingCat.ofHom e.symm.toRingHom = 𝟙 _ := (Scheme.ΓSpecIso (.of A)).inv_hom_id
  rw [hid, Spec.map_id, Category.comp_id]

private lemma exists_affine_comparison (I : Ideal R) :
    ∃ e : AffineBlowup (centerIdeal I) ≅ (center I).blowup,
      e.hom ≫ (center I).blowupMap = AffineBlowup.toSpec (centerIdeal I) :=
  exists_comparison _ _ (Scheme.IdealSheafData.ideal_top_ofIdealTop _)

private lemma ideal_top_comap_specMap {A B : Type u} [CommRing A] [CommRing B]
    (K : Ideal A) (J : (Spec (.of A)).IdealSheafData)
    (hJ : J.ideal ⟨⊤, isAffineOpen_top _⟩ =
      K.map (Scheme.ΓSpecIso (.of A)).inv.hom) (φ : A →+* B) :
    (J.comap (Spec.map (CommRingCat.ofHom φ))).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (K.map φ).map (Scheme.ΓSpecIso (.of B)).inv.hom := by
  rw [Scheme.IdealSheafData.ideal_top_comap_of_isAffine, hJ,
    Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)).symm

private lemma ker_strictTransformMap_eq_ker_lift {X Y : Scheme.{u}}
    (J : X.IdealSheafData) (g : Y ⟶ X) {ρ : (J.comap g).blowup ⟶ J.blowup}
    (hρ : (J.comap g).blowupMap ≫ g = ρ ≫ J.blowupMap) :
    (strictTransformMap g J.blowupMap J.support.compl).ker = ρ.ker := by
  change (AlgebraicGeometry.strictTransformι g J.blowupMap J.support.compl ≫
    Limits.pullback.snd g J.blowupMap).ker = _
  change (J.strictTransformι g ≫ Limits.pullback.snd g J.blowupMap).ker = _
  rw [Scheme.Hom.ker_comp,
    Scheme.IdealSheafData.StrictTransformChart.ker_strictTransformι_eq_ker_pullbackLift hρ,
    ← Scheme.Hom.ker_comp, Limits.pullback.lift_snd]

private lemma ker_affine_transform {A B : Type u} [CommRing A] [CommRing B]
    (K : Ideal A) (J : (Spec (.of A)).IdealSheafData)
    (hJ : J.ideal ⟨⊤, isAffineOpen_top _⟩ =
      K.map (Scheme.ΓSpecIso (.of A)).inv.hom) (φ : A →+* B)
    (e : AffineBlowup K ≅ J.blowup)
    (he : e.hom ≫ J.blowupMap = AffineBlowup.toSpec K) :
    (strictTransformMap (Spec.map (CommRingCat.ofHom φ)) J.blowupMap
      J.support.compl).ker.comap e.hom = (AffineBlowup.hom φ rfl).ker := by
  let g := Spec.map (CommRingCat.ofHom φ)
  obtain ⟨e', he'⟩ := exists_comparison (K.map φ) (J.comap g)
    (ideal_top_comap_specMap K J hJ φ)
  let ρ := e'.inv ≫ AffineBlowup.hom φ rfl ≫ e.hom
  have hρ : (J.comap g).blowupMap ≫ g = ρ ≫ J.blowupMap := by
    dsimp only [ρ]
    rw [Category.assoc, Category.assoc, he, AffineBlowup.hom_toSpec]
    rw [← he', ← Category.assoc, Iso.inv_hom_id_assoc]
  rw [ker_strictTransformMap_eq_ker_lift J g hρ]
  have hker : ρ.ker = (AffineBlowup.hom φ rfl ≫ e.hom).ker :=
    Scheme.Hom.ker_comp_of_isIso _ _
  rw [hker, Scheme.Hom.ker_comp]
  exact Scheme.IdealSheafData.comap_map _ _

private lemma isClosedImmersion_affineHom {A B : Type u} [CommRing A] [CommRing B]
    (K : Ideal A) (φ : A →+* B) (hφ : Function.Surjective φ) :
    IsClosedImmersion (AffineBlowup.hom (I := K) φ rfl) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom φ)) :=
    IsClosedImmersion.spec_of_surjective _ hφ
  have := AffineBlowup.isClosedImmersion_pullbackLift (I := K) φ rfl
  let l := Limits.pullback.lift (AffineBlowup.toSpec (K.map φ))
    (AffineBlowup.hom φ rfl) (AffineBlowup.hom_toSpec φ rfl).symm
  have hc : IsClosedImmersion
      (l ≫ Limits.pullback.snd (Spec.map (CommRingCat.ofHom φ)) (AffineBlowup.toSpec K)) := by
    dsimp only [l]
    infer_instance
  simpa only [l, Limits.pullback.lift_snd] using hc

private lemma chartRing_ker_hom {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (K : Ideal A) {a : A} (ha : a ∈ K)
    [QuasiCompact (AffineBlowup.hom (I := K) (algebraMap A B) rfl)] :
    (AffineBlowup.hom (I := K) (algebraMap A B) rfl).ker.comap
        (AffineBlowup.chartRingι K ha) =
      (Spec.map (CommRingCat.ofHom
        ((AffineBlowup.strictChartMap B K a ha).toRingHom.comp
          Algebra.TensorProduct.includeRight.toRingHom))).ker := by
  let κ := (AffineBlowup.strictChartMap B K a ha).toRingHom.comp
    Algebra.TensorProduct.includeRight.toRingHom
  have hw : AffineBlowup.baseChangeChartRingι B K ha ≫
      AffineBlowup.hom (algebraMap A B) rfl =
        Spec.map (CommRingCat.ofHom κ) ≫ AffineBlowup.chartRingι K ha := by
    have w := congrArg (fun k ↦ k ≫
      Limits.pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap A B)))
        (AffineBlowup.toSpec K)) (AffineBlowup.isPullback_baseChangeChartι B K ha).w
    simp only [Category.assoc, AffineBlowup.baseChangeLift, Limits.pullback.lift_snd,
      AffineBlowup.baseChangeChartι_snd] at w
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp] at w
    exact w.symm
  have hs : IsPullback (AffineBlowup.baseChangeChartRingι B K ha)
      (Spec.map (CommRingCat.ofHom κ)) (AffineBlowup.hom (algebraMap A B) rfl)
      (AffineBlowup.chartRingι K ha) := by
    apply IsPullback.flip
    apply IsOpenImmersion.isPullback _ _ _ _ hw
    rw [AffineBlowup.opensRange_chartRingιOfEq, AffineBlowup.opensRange_chartRingιOfEq,
      AffineBlowup.opensRange_chart, AffineBlowup.opensRange_chart]
    exact Proj.map_preimage_basicOpen (reesGrading.hom (algebraMap A B) rfl)
      (reesGrading.irrelevant_le_map_hom (algebraMap A B) rfl) _
  exact Scheme.Hom.comap_ker_of_isPullback hs

private noncomputable abbrev hyperplaneRing (R : Type u) [CommRing R] :=
  Polynomial R ⧸ (Ideal.span {Polynomial.X} : Ideal (Polynomial R))

private noncomputable abbrev hyperplaneMap : Polynomial R →+* hyperplaneRing R :=
  Ideal.Quotient.mk _

private lemma hyperplaneMap_X : hyperplaneMap (R := R) Polynomial.X = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

private lemma hyperplaneEval_wellDefined :
    (Ideal.span {Polynomial.X} : Ideal (Polynomial R)) ≤
      RingHom.ker (Polynomial.evalRingHom 0) := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  simp

private noncomputable def hyperplaneEval : hyperplaneRing R →+* R :=
  Ideal.Quotient.lift _ (Polynomial.evalRingHom 0) hyperplaneEval_wellDefined

private lemma hyperplaneMap_C_injective :
    Function.Injective ((hyperplaneMap (R := R)).comp Polynomial.C) := by
  intro x y h
  have := congrArg (hyperplaneEval (R := R)) h
  simpa [hyperplaneEval, hyperplaneMap] using this

private lemma awayMap_hyperplane_C (a : R) :
    (Localization.awayMap (hyperplaneMap (R := R)) (Polynomial.C a)).comp
        (Localization.awayMap Polynomial.C a) =
      Localization.awayMap ((hyperplaneMap (R := R)).comp Polynomial.C) a := by
  apply IsLocalization.ringHom_ext (Submonoid.powers a)
  ext r
  simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]

private lemma chartMap_coe {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (K : Ideal A) {a : A} (ha : a ∈ K) (c : AffineBlowup.chartRing K a) :
    ((AffineBlowup.strictChartMap B K a ha)
      (Algebra.TensorProduct.includeRight c) : Localization.Away (algebraMap A B a)) =
        Localization.awayMap (algebraMap A B) a c.val := by
  change AffineBlowup.baseChangeChartToAway B K a (1 ⊗ₜ c) = _
  rw [AffineBlowup.baseChangeChartToAway_tmul]
  simp only [map_one, one_mul]
  rfl

private noncomputable def expandMap (a : R) :
    Polynomial R →+* Polynomial (Localization.Away a) :=
  Polynomial.eval₂RingHom (Polynomial.C.comp (algebraMap R (Localization.Away a)))
    (Polynomial.C (algebraMap R (Localization.Away a) a) * Polynomial.X)

private lemma expandMap_unit (a : R) :
    expandMap a (Polynomial.C a) *
      Polynomial.C (IsLocalization.Away.invSelf a) = 1 := by
  simp only [expandMap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    RingHom.comp_apply, ← Polynomial.C_mul]
  rw [IsLocalization.Away.mul_invSelf, Polynomial.C_1]

private noncomputable def expandLift (a : R) :
    Localization.Away (Polynomial.C a) →+* Polynomial (Localization.Away a) :=
  Localization.awayLift (expandMap a) (Polynomial.C a)
    (isUnit_iff_exists_inv.mpr ⟨_, expandMap_unit a⟩)

private lemma expandLift_algebraMap (a : R) (p : Polynomial R) :
    expandLift a (algebraMap (Polynomial R) _ p) = expandMap a p :=
  IsLocalization.Away.lift_eq (Polynomial.C a)
    (isUnit_iff_exists_inv.mpr ⟨_, expandMap_unit a⟩) p

private lemma expandLift_fraction (a : R) (n : ℕ) (p : Polynomial R) :
    expandLift a (AffineBlowup.chartFraction (Polynomial.C a) n p) =
      expandMap a p * Polynomial.C (IsLocalization.Away.invSelf a) ^ n :=
  Localization.awayLift_mk (expandMap a) (Polynomial.C a) p _ (expandMap_unit a) n

private lemma expandLift_constant (a : R) (c : Localization.Away a) :
    expandLift a (Localization.awayMap Polynomial.C a c) = Polynomial.C c := by
  have h : (expandLift a).comp (Localization.awayMap Polynomial.C a) =
      Polynomial.C := by
    apply IsLocalization.ringHom_ext (Submonoid.powers a)
    ext r
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq,
      expandLift_algebraMap, expandMap]
  exact DFunLike.congr_fun h c

private lemma expandLift_parameter (a : R) :
    expandLift a (AffineBlowup.chartFraction (Polynomial.C a) 1 Polynomial.X) =
      Polynomial.X := by
  rw [expandLift_fraction]
  simp only [expandMap, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, pow_one]
  rw [mul_comm _ (Polynomial.C _), ← mul_assoc, ← Polynomial.C_mul,
    mul_comm (IsLocalization.Away.invSelf a), IsLocalization.Away.mul_invSelf,
    Polynomial.C_1, one_mul]

private noncomputable def substitution (I : Ideal R) (a : R) :
    Polynomial (AffineBlowup.chartRing I a) →+* Localization.Away (Polynomial.C a) :=
  Polynomial.eval₂RingHom
    ((Localization.awayMap Polynomial.C a).comp (AffineBlowup.chartRing I a).val.toRingHom)
    (AffineBlowup.chartFraction (Polynomial.C a) 1 Polynomial.X)

private lemma substitution_injective (I : Ideal R) (a : R) :
    Function.Injective (substitution I a) := by
  have h : (expandLift a).comp (substitution I a) =
      Polynomial.mapRingHom (AffineBlowup.chartRing I a).val.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro c
      simp [substitution, expandLift_constant]
    · simp [substitution, expandLift_parameter]
  intro p q hpq
  apply Polynomial.map_injective
    (f := (AffineBlowup.chartRing I a).val.toRingHom) Subtype.val_injective
  change Polynomial.mapRingHom _ p = Polynomial.mapRingHom _ q
  rw [← h]
  exact congrArg (expandLift a) hpq

private lemma awayMap_fraction (a x : R) (n : ℕ) :
    Localization.awayMap Polynomial.C a (AffineBlowup.chartFraction a n x) =
      AffineBlowup.chartFraction (Polynomial.C a) n (Polynomial.C x) := by
  simp only [AffineBlowup.chartFraction, Localization.mk_eq_mk', Localization.awayMap,
    IsLocalization.Away.map, IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  exact map_pow _ _ _

private lemma algebraMap_mul_fraction {A : Type u} [CommRing A] (a x : A) :
    algebraMap A (Localization.Away a) a * AffineBlowup.chartFraction a 1 x =
      algebraMap A (Localization.Away a) x := by
  rw [← AffineBlowup.chartFraction_zero, ← AffineBlowup.chartFraction_mul,
    ← AffineBlowup.chartFraction_zero, AffineBlowup.chartFraction_eq_iff]
  exact ⟨0, by simp⟩

private lemma awayMap_algebraMap (a r : R) :
    Localization.awayMap Polynomial.C a (algebraMap R _ r) =
      algebraMap (Polynomial R) _ (Polynomial.C r) :=
  IsLocalization.map_eq _ _

private lemma substitution_mem (I : Ideal R) (a : R)
    (p : Polynomial (AffineBlowup.chartRing I a)) :
    substitution I a p ∈ AffineBlowup.chartRing (centerIdeal I) (Polynomial.C a) := by
  let S := AffineBlowup.chartRing (centerIdeal I) (Polynomial.C a)
  have hc (c : AffineBlowup.chartRing I a) :
      Localization.awayMap Polynomial.C a c.val ∈ S := by
    obtain ⟨c, hc⟩ := c
    change Localization.awayMap Polynomial.C a c ∈ S
    induction hc using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨b, rfl⟩ := hx
      rw [awayMap_fraction]
      exact Algebra.subset_adjoin ⟨constant I b, rfl⟩
    | algebraMap r =>
      rw [awayMap_algebraMap]
      exact S.algebraMap_mem _
    | add x y _ _ hx hy =>
      rw [map_add]
      exact S.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact S.mul_mem hx hy
  have hx : AffineBlowup.chartFraction (Polynomial.C a) 1 Polynomial.X ∈ S :=
    Algebra.subset_adjoin ⟨parameter I, rfl⟩
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact S.add_mem hp hq
  | monomial n c =>
    rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
    exact S.mul_mem (by simpa [substitution] using hc c)
      (by simpa [substitution] using S.pow_mem hx n)

private lemma chartRing_le_substitution_range (I : Ideal R) (a : R) :
    (AffineBlowup.chartRing (centerIdeal I) (Polynomial.C a) :
      Set (Localization.Away (Polynomial.C a))) ⊆ Set.range (substitution I a) := by
  let q := substitution I a
  have hC (r : R) : algebraMap (Polynomial R) _ (Polynomial.C r) ∈ q.rangeS := by
    refine ⟨Polynomial.C (algebraMap R (AffineBlowup.chartRing I a) r), ?_⟩
    simpa [q, substitution] using awayMap_algebraMap a r
  have hX : algebraMap (Polynomial R) _ Polynomial.X ∈ q.rangeS := by
    refine ⟨Polynomial.C (algebraMap R (AffineBlowup.chartRing I a) a) * Polynomial.X, ?_⟩
    simpa [q, substitution, awayMap_algebraMap] using
      algebraMap_mul_fraction (Polynomial.C a) Polynomial.X
  let S : Subalgebra (Polynomial R) (Localization.Away (Polynomial.C a)) :=
    { q.rangeS with
      algebraMap_mem' := fun p ↦ by
        induction p using Polynomial.induction_on' with
        | add p p' hp hp' =>
          rw [map_add]
          exact q.rangeS.add_mem hp hp'
        | monomial n r =>
          rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow]
          exact q.rangeS.mul_mem (hC r) (q.rangeS.pow_mem hX n) }
  have hmul (p p' : Polynomial R) :
      AffineBlowup.chartFraction (Polynomial.C a) 1 (p * p') =
        algebraMap (Polynomial R) _ p *
          AffineBlowup.chartFraction (Polynomial.C a) 1 p' := by
    rw [← AffineBlowup.chartFraction_zero, ← AffineBlowup.chartFraction_mul]
  let K : Ideal (Polynomial R) :=
    { carrier := {p | AffineBlowup.chartFraction (Polynomial.C a) 1 p ∈ S}
      zero_mem' := by
        change AffineBlowup.chartFraction (Polynomial.C a) 1 0 ∈ S
        rw [AffineBlowup.chartFraction, Localization.mk_zero]
        exact S.zero_mem
      add_mem' := by
        intro p p' hp hp'
        change AffineBlowup.chartFraction (Polynomial.C a) 1 (p + p') ∈ S
        rw [AffineBlowup.chartFraction_add]
        exact S.add_mem hp hp'
      smul_mem' := by
        intro p p' hp'
        change AffineBlowup.chartFraction (Polynomial.C a) 1 (p * p') ∈ S
        rw [hmul]
        exact S.mul_mem (S.algebraMap_mem p) hp' }
  have hK : centerIdeal I ≤ K := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro b hb
      change AffineBlowup.chartFraction (Polynomial.C a) 1 (Polynomial.C b) ∈ q.rangeS
      refine ⟨Polynomial.C ⟨AffineBlowup.chartFraction a 1 b,
        Algebra.subset_adjoin ⟨⟨b, hb⟩, rfl⟩⟩, ?_⟩
      simpa [q, substitution] using awayMap_fraction a b 1
    · apply Ideal.span_le.mpr
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      exact ⟨Polynomial.X, by simp [q, substitution]⟩
  have hle : AffineBlowup.chartRing (centerIdeal I) (Polynomial.C a) ≤ S := by
    apply Algebra.adjoin_le
    rintro _ ⟨b, rfl⟩
    exact hK b.2
  exact hle

private lemma exists_constant_chart (I : Ideal R) (a : R) :
    ∃ θ : Polynomial (AffineBlowup.chartRing I a) ≃+*
        AffineBlowup.chartRing (centerIdeal I) (Polynomial.C a),
      (∀ c : AffineBlowup.chartRing I a,
        (θ (Polynomial.C c) : Localization.Away (Polynomial.C a)) =
          Localization.awayMap Polynomial.C a c.val) ∧
      (θ Polynomial.X : Localization.Away (Polynomial.C a)) =
        AffineBlowup.chartFraction (Polynomial.C a) 1 Polynomial.X := by
  let q := (substitution I a).codRestrict
    (AffineBlowup.chartRing (centerIdeal I) (Polynomial.C a)) (substitution_mem I a)
  have hinj : Function.Injective q := by
    intro p p' h
    exact substitution_injective I a (congrArg Subtype.val h)
  have hsurj : Function.Surjective q := by
    intro c
    obtain ⟨p, hp⟩ := chartRing_le_substitution_range I a c.2
    exact ⟨p, Subtype.ext hp⟩
  exact ⟨RingEquiv.ofBijective q ⟨hinj, hsurj⟩,
    fun c ↦ Polynomial.eval₂_C _ _, Polynomial.eval₂_X _ _⟩

set_option backward.isDefEq.respectTransparency false in
private lemma chartMap_constant_kernel (I : Ideal R) (a : I)
    (θ : Polynomial (AffineBlowup.chartRing I (a : R)) ≃+*
      AffineBlowup.chartRing (centerIdeal I) (Polynomial.C (a : R)))
    (hC : ∀ c, (θ (Polynomial.C c) : Localization.Away (Polynomial.C (a : R))) =
      Localization.awayMap Polynomial.C (a : R) c.val)
    (hX : (θ Polynomial.X : Localization.Away (Polynomial.C (a : R))) =
      AffineBlowup.chartFraction (Polynomial.C (a : R)) 1 Polynomial.X) :
    let B := hyperplaneRing R
    let κ := (AffineBlowup.strictChartMap B (centerIdeal I) (Polynomial.C (a : R))
      (constant I a).2).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
    RingHom.ker (κ.comp θ.toRingHom) = Ideal.span {Polynomial.X} := by
  let B := hyperplaneRing R
  let κ := (AffineBlowup.strictChartMap B (centerIdeal I) (Polynomial.C (a : R))
    (constant I a).2).toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom
  let δ := (hyperplaneMap (R := R)).comp Polynomial.C
  let α := Localization.awayMap δ (a : R)
  have hinj : Function.Injective α := by
    rw [Localization.awayMap_injective_iff]
    intro r hr
    exact ⟨0, by simpa using (map_eq_zero_iff _ hyperplaneMap_C_injective).mp hr⟩
  have hκ (c : AffineBlowup.chartRing (centerIdeal I) (Polynomial.C (a : R))) :
      (κ c : Localization.Away (δ a)) =
        Localization.awayMap (algebraMap (Polynomial R) B) (Polynomial.C (a : R)) c.val :=
    chartMap_coe (centerIdeal I) (constant I a).2 c
  have h : ((AffineBlowup.chartRing ((centerIdeal I).map (algebraMap (Polynomial R) B))
      (algebraMap (Polynomial R) B (Polynomial.C (a : R)))).val.toRingHom.comp
        (κ.comp θ.toRingHom)) =
      Polynomial.eval₂RingHom (α.comp (AffineBlowup.chartRing I (a : R)).val.toRingHom) 0 := by
    apply Polynomial.ringHom_ext
    · intro c
      change (κ (θ (Polynomial.C c)) : Localization.Away (δ a)) = _
      calc
        (κ (θ (Polynomial.C c)) : Localization.Away (δ a)) = α c.val := by
          rw [hκ, hC]
          exact congrArg (fun q : Localization.Away (a : R) →+*
            Localization.Away (δ a) ↦ q c.val) (awayMap_hyperplane_C (a : R))
        _ = _ := (Polynomial.eval₂_C
          (α.comp (AffineBlowup.chartRing I (a : R)).val.toRingHom) 0).symm
    · change (κ (θ Polynomial.X) : Localization.Away (δ a)) = _
      calc
        (κ (θ Polynomial.X) : Localization.Away (δ a)) = 0 := by
          rw [hκ, hX]
          change AffineBlowup.awayBaseChange B (Polynomial.C (a : R))
            (AffineBlowup.chartFraction (Polynomial.C (a : R)) 1 Polynomial.X) = _
          rw [AffineBlowup.awayBaseChange_chartFraction]
          simp only [AffineBlowup.chartFraction, Localization.mk_zero,
            show algebraMap (Polynomial R) B Polynomial.X = 0 from hyperplaneMap_X]
        _ = _ := (Polynomial.eval₂_X
          (α.comp (AffineBlowup.chartRing I (a : R)).val.toRingHom) 0).symm
  ext p
  change κ (θ p) = 0 ↔ _
  rw [← Subtype.val_injective.eq_iff]
  change (((AffineBlowup.chartRing _ _).val.toRingHom.comp
    (κ.comp θ.toRingHom)) p = 0) ↔ _
  rw [h]
  change Polynomial.eval₂ _ 0 p = 0 ↔ _
  rw [Polynomial.eval₂_at_zero]
  change α (p.coeff 0).val = 0 ↔ _
  rw [map_eq_zero_iff _ hinj]
  change (AffineBlowup.chartRing I (a : R)).val.toRingHom (p.coeff 0) = 0 ↔ _
  rw [map_eq_zero_iff _ Subtype.val_injective]
  rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff]

set_option backward.isDefEq.respectTransparency false in
private lemma chartRing_preimage_chart {A : Type u} [CommRing A] (K : Ideal A)
    {a b : A} (ha : a ∈ K) (hb : b ∈ K) :
    (AffineBlowup.chartRingι K ha) ⁻¹ᵁ (AffineBlowup.chartRingι K hb).opensRange =
      PrimeSpectrum.basicOpen ⟨AffineBlowup.chartFraction a 1 b,
        Algebra.subset_adjoin ⟨⟨b, hb⟩, rfl⟩⟩ := by
  rw [AffineBlowup.opensRange_chartRingιOfEq, AffineBlowup.opensRange_chart]
  change (Spec.map (CommRingCat.ofHom
    (AffineBlowup.homogeneousAwayEquivChart K ha).toRingHom) ≫
      Proj.awayι (reesGrading K) _ _ one_pos) ⁻¹ᵁ _ = _
  rw [Scheme.Hom.comp_preimage]
  have hp := Proj.awayι_preimage_basicOpen (reesGrading K) (reesX_mem K a ha) one_pos
    (reesX_mem K b hb) one_pos
  trans (Spec.map (CommRingCat.ofHom
    (AffineBlowup.homogeneousAwayEquivChart K ha).toRingHom)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen
        (HomogeneousLocalization.Away.isLocalizationElem (reesX_mem K a ha)
          (reesX_mem K b hb))
  · exact congrArg (fun U ↦ (Spec.map (CommRingCat.ofHom
      (AffineBlowup.homogeneousAwayEquivChart K ha).toRingHom)) ⁻¹ᵁ U) hp
  change TopologicalSpace.Opens.comap
    ⟨PrimeSpectrum.comap (AffineBlowup.homogeneousAwayEquivChart K ha).toRingHom, _⟩ _ = _
  rw [PrimeSpectrum.comap_basicOpen]
  congr 1
  apply Subtype.ext
  change (AffineBlowup.homogeneousAwayToChart K ha
    (HomogeneousLocalization.Away.mk (reesGrading K) (reesX_mem K a ha) 1
      (reesX K b hb ^ 1) _) : Localization.Away a) = _
  simp only [pow_one]
  exact AffineBlowup.coe_homogeneousAwayToChart_mk K ha b (by simpa using hb) _

private lemma comap_ker_ringEquiv {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (e : A ≃+* B) (κ : B →+* C) :
    (Spec.map (CommRingCat.ofHom κ)).ker.comap
        (Spec.map (CommRingCat.ofHom e.symm.toRingHom)) =
      (Spec.map (CommRingCat.ofHom (κ.comp e.toRingHom))).ker := by
  have : IsIso (CommRingCat.ofHom e.symm.toRingHom) :=
    e.symm.toCommRingCatIso.isIso_hom
  apply Scheme.Hom.comap_ker_of_isPullback
    (p := 𝟙 (Spec (.of C)))
  apply IsPullback.of_horiz_isIso
  constructor
  rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact (congrArg κ (e.apply_symm_apply x)).symm

private lemma parameter_transformIdeal (I : Ideal R)
    (e : AffineBlowup (centerIdeal I) ≅ (center I).blowup)
    (he : e.hom ≫ (center I).blowupMap = AffineBlowup.toSpec (centerIdeal I)) :
    (transformIdeal I).comap (AffineBlowup.chartRingι (centerIdeal I) (parameter I).2 ≫
      e.hom) = ⊤ := by
  let B := hyperplaneRing R
  have hc := isClosedImmersion_affineHom (centerIdeal I)
    (hyperplaneMap (R := R)) Ideal.Quotient.mk_surjective
  rw [Scheme.IdealSheafData.comap_comp]
  change ((strictTransformMap (Spec.map (CommRingCat.ofHom (hyperplaneMap (R := R))))
    (center I).blowupMap (center I).support.compl).ker.comap e.hom).comap _ = _
  erw [ker_affine_transform (centerIdeal I) (center I)
    (Scheme.IdealSheafData.ideal_top_ofIdealTop _) (hyperplaneMap (R := R)) e he,
    chartRing_ker_hom]
  have hzero : algebraMap (Polynomial R) B (parameter I) = 0 := hyperplaneMap_X
  have : Subsingleton (Localization.Away
      (algebraMap (Polynomial R) B (parameter I))) :=
    IsLocalization.subsingleton
      (M := Submonoid.powers (algebraMap (Polynomial R) B (parameter I)))
      (S := Localization.Away (algebraMap (Polynomial R) B (parameter I))) (by
        exact ⟨1, by simpa using hzero⟩)
  have : Subsingleton (AffineBlowup.chartRing
      ((centerIdeal I).map (algebraMap (Polynomial R) B))
      (algebraMap (Polynomial R) B (parameter I))) :=
    Function.Injective.subsingleton Subtype.val_injective
  have : IsEmpty (Spec (.of (AffineBlowup.chartRing
      ((centerIdeal I).map (algebraMap (Polynomial R) B))
      (algebraMap (Polynomial R) B (parameter I))))) :=
    PrimeSpectrum.isEmpty_iff_subsingleton.mpr inferInstance
  exact Scheme.ker_eq_top_of_isEmpty _

private lemma constant_transformIdeal (I : Ideal R) (a : I)
    (e : AffineBlowup (centerIdeal I) ≅ (center I).blowup)
    (he : e.hom ≫ (center I).blowupMap = AffineBlowup.toSpec (centerIdeal I))
    (θ : Polynomial (AffineBlowup.chartRing I (a : R)) ≃+*
      AffineBlowup.chartRing (centerIdeal I) (Polynomial.C (a : R)))
    (hC : ∀ c, (θ (Polynomial.C c) : Localization.Away (Polynomial.C (a : R))) =
      Localization.awayMap Polynomial.C (a : R) c.val)
    (hX : (θ Polynomial.X : Localization.Away (Polynomial.C (a : R))) =
      AffineBlowup.chartFraction (Polynomial.C (a : R)) 1 Polynomial.X) :
    (transformIdeal I).comap (Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫
        AffineBlowup.chartRingι (centerIdeal I) (constant I a).2 ≫ e.hom) =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (Ideal.span {Polynomial.X} :
          Ideal (Polynomial (AffineBlowup.chartRing I (a : R))))))).ker := by
  let B := hyperplaneRing R
  have hc := isClosedImmersion_affineHom (centerIdeal I)
    (hyperplaneMap (R := R)) Ideal.Quotient.mk_surjective
  rw [Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp]
  change (((strictTransformMap (Spec.map (CommRingCat.ofHom (hyperplaneMap (R := R))))
    (center I).blowupMap (center I).support.compl).ker.comap e.hom).comap _).comap _ = _
  erw [ker_affine_transform (centerIdeal I) (center I)
    (Scheme.IdealSheafData.ideal_top_ofIdealTop _) (hyperplaneMap (R := R)) e he,
    chartRing_ker_hom, comap_ker_ringEquiv]
  apply Scheme.Hom.ker_specMap_eq_of_ker_eq
  change RingHom.ker (_ : Polynomial (AffineBlowup.chartRing I (a : R)) →+* _) = _
  erw [Ideal.mk_ker]
  exact chartMap_constant_kernel I a θ hC hX

private lemma chart_cover (I : Ideal R) (m : ℕ) (f : Fin m → I)
    (hf : Ideal.span (Set.range fun i ↦ (f i : R)) = I)
    (p : AffineBlowup (centerIdeal I)) :
    p ∈ (AffineBlowup.chartRingι (centerIdeal I) (parameter I).2).opensRange ∨
      ∃ i, p ∈ (AffineBlowup.chartRingι (centerIdeal I) (constant I (f i)).2).opensRange := by
  classical
  let s : Finset (Polynomial R) :=
    insert Polynomial.X (Finset.univ.image fun i : Fin m ↦ Polynomial.C (f i : R))
  have hs : (s : Set (Polynomial R)) =
      {Polynomial.X} ∪ Polynomial.C '' Set.range (fun i ↦ (f i : R)) := by
    ext p
    simp [s]
  have hspan : Ideal.span (s : Set (Polynomial R)) = centerIdeal I := by
    rw [hs, Ideal.span_union, ← Ideal.map_span, hf]
    exact sup_comm _ _
  have hp : p ∈ (⊤ : (AffineBlowup (centerIdeal I)).Opens) := trivial
  rw [← AffineBlowup.iSup_basicOpen_reesX_eq_top_of_span hspan] at hp
  obtain ⟨⟨a, ha⟩, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hp
  rcases Finset.mem_insert.mp ha with rfl | ha
  · left
    rwa [AffineBlowup.opensRange_chartRingιOfEq, AffineBlowup.opensRange_chart]
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    exact Or.inr ⟨i, by
      rwa [AffineBlowup.opensRange_chartRingιOfEq, AffineBlowup.opensRange_chart]⟩

private lemma quotient_ker_support {A : Type u} [CommRing A] (x : A) :
    ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {x})))).ker.support :
      Set (Spec (.of A))) = {p | x ∈ p.asIdeal} := by
  rw [Scheme.Hom.support_ker]
  change closure (Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span {x})))) = _
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, PrimeSpectrum.zeroLocus_span, (PrimeSpectrum.isClosed_zeroLocus _).closure_eq]
  ext p
  simp only [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
  rfl

private lemma preimage_range_comp_iso {W X Y Z : Scheme.{u}} (e : X ≅ Y)
    (g : W ⟶ X) (f : Z ⟶ X) :
    (f ≫ e.hom) ⁻¹' Set.range (g ≫ e.hom) = f ⁻¹' Set.range g := by
  ext p
  simp only [Set.mem_preimage, Set.mem_range, Scheme.Hom.comp_apply]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, e.hom.homeomorph.injective hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg e.hom hy⟩

private lemma constant_chart_overlap (I : Ideal R) (a : I)
    (e : AffineBlowup (centerIdeal I) ≅ (center I).blowup)
    (θ : Polynomial (AffineBlowup.chartRing I (a : R)) ≃+*
      AffineBlowup.chartRing (centerIdeal I) (Polynomial.C (a : R)))
    (hX : (θ Polynomial.X : Localization.Away (Polynomial.C (a : R))) =
      AffineBlowup.chartFraction (Polynomial.C (a : R)) 1 Polynomial.X) :
    (Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫
        AffineBlowup.chartRingι (centerIdeal I) (constant I a).2 ≫ e.hom) ⁻¹'
      Set.range (AffineBlowup.chartRingι (centerIdeal I) (parameter I).2 ≫ e.hom) =
        {p | Polynomial.X ∉ p.asIdeal} := by
  rw [← Category.assoc, preimage_range_comp_iso]
  have hpre := chartRing_preimage_chart (centerIdeal I) (constant I a).2 (parameter I).2
  have hv : θ Polynomial.X =
      (⟨AffineBlowup.chartFraction (Polynomial.C (a : R)) 1 Polynomial.X,
        Algebra.subset_adjoin ⟨parameter I, rfl⟩⟩ :
          AffineBlowup.chartRing (centerIdeal I) (Polynomial.C (a : R))) :=
    Subtype.ext hX
  have hop : (Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫
      AffineBlowup.chartRingι (centerIdeal I) (constant I a).2) ⁻¹ᵁ
        (AffineBlowup.chartRingι (centerIdeal I) (parameter I).2).opensRange =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial (AffineBlowup.chartRing I (a : R))) := by
    erw [Scheme.Hom.comp_preimage, hpre]
    change TopologicalSpace.Opens.comap
      ⟨PrimeSpectrum.comap θ.symm.toRingHom, _⟩ _ = _
    rw [PrimeSpectrum.comap_basicOpen]
    congr 1
    change θ.symm _ = Polynomial.X
    apply θ.injective
    rw [RingEquiv.apply_symm_apply]
    exact hv.symm
  have hset := congrArg (fun U : (Spec (.of
      (Polynomial (AffineBlowup.chartRing I (a : R))))).Opens ↦
        (U : Set (Spec (.of (Polynomial (AffineBlowup.chartRing I (a : R))))))) hop
  simp only [Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange] at hset
  exact hset.trans (Set.ext fun p ↦ PrimeSpectrum.mem_basicOpen _ p)

private lemma chartRing_parameter (I : Ideal R) :
    AffineBlowup.chartRing (centerIdeal I) Polynomial.X =
      Algebra.adjoin (Polynomial R)
        (Set.range fun a : I ↦
          AffineBlowup.chartFraction (Polynomial.X : Polynomial R) 1
            (Polynomial.C (a : R))) := by
  let S := Algebra.adjoin (Polynomial R)
    (Set.range fun a : I ↦
      AffineBlowup.chartFraction (Polynomial.X : Polynomial R) 1
        (Polynomial.C (a : R)))
  have hmul (p q : Polynomial R) :
      AffineBlowup.chartFraction Polynomial.X 1 (p * q) =
        algebraMap (Polynomial R) _ p *
          AffineBlowup.chartFraction Polynomial.X 1 q := by
    rw [← AffineBlowup.chartFraction_zero, ← AffineBlowup.chartFraction_mul]
  let K : Ideal (Polynomial R) :=
    { carrier := {p | AffineBlowup.chartFraction Polynomial.X 1 p ∈ S}
      zero_mem' := by
        change AffineBlowup.chartFraction Polynomial.X 1 0 ∈ S
        rw [AffineBlowup.chartFraction, Localization.mk_zero]
        exact S.zero_mem
      add_mem' := by
        intro p q hp hq
        change AffineBlowup.chartFraction Polynomial.X 1 (p + q) ∈ S
        rw [AffineBlowup.chartFraction_add]
        exact S.add_mem hp hq
      smul_mem' := by
        intro p q hq
        change AffineBlowup.chartFraction Polynomial.X 1 (p * q) ∈ S
        rw [hmul]
        exact S.mul_mem (S.algebraMap_mem p) hq }
  have hK : centerIdeal I ≤ K := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      exact Algebra.subset_adjoin ⟨⟨a, ha⟩, rfl⟩
    · apply Ideal.span_le.mpr
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      change AffineBlowup.chartFraction Polynomial.X 1 Polynomial.X ∈ S
      have h : AffineBlowup.chartFraction Polynomial.X 1 Polynomial.X =
          (1 : Localization.Away (Polynomial.X : Polynomial R)) := by
        calc
          _ = AffineBlowup.chartFraction Polynomial.X 0 1 := by
            rw [AffineBlowup.chartFraction_eq_iff]
            exact ⟨0, by simp⟩
          _ = 1 := by rw [AffineBlowup.chartFraction_zero, map_one]
      rw [h]
      exact S.one_mem
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro _ ⟨a, rfl⟩
    exact hK a.2
  · apply Algebra.adjoin_le
    rintro _ ⟨a, rfl⟩
    exact Algebra.subset_adjoin ⟨constant I a, rfl⟩

/-- The strict-transform complement is exactly the parameter chart, including the
scheme-theoretic calculation on every generator chart. Source: Stacks, Tags 0804 and 080D
(blueprint: lem-pur-dnc-affine-blowup-complement).

Proof plan:
1. The global blow-up over this affine base is the affine Rees blow-up, by
`def-nagata-global-blowup`, its gluing datum and local model. The standard charts cover it
by `prop-nagata-affine-blowup-chart` and `prop-nagata-affine-blowup-chart-cover`.
The map `def-nagata-homogeneous-away-to-chart` sends the homogeneous fraction to `x/a`.
2. On an `f`-chart put `C = R[I/f]`. Substitution `v ↦ t/f` gives `C[v] ≃ A[J/f]`.
It is onto because `t = fv`; it is one-to-one by comparison of polynomial coefficients
inside `R_f[t]`, since `f` is a unit in `R_f`. This includes the zero localization.
3. The strict transform is the schematic closure of the hyperplane away from the centre.
The open immersion used for the closure is quasi-compact since the ideal has finitely many
generators. By `lemma-nagata-scheme-image-restrict-open`, compute its ideal on each chart
as the restriction kernel, using `def-nagata-scheme-theoretic-closure` and
`def-nagata-scheme-theoretic-image`.
4. On the parameter chart the centre ideal is `(t)`, and `V(t) ∩ D(t)` is empty.
Its closure ideal is the unit ideal.
5. On the `f`-chart the centre is `(f)` and the hyperplane is `V(fv)`. Off the centre
its ring is `R_f[v]/(v) = R_f`. The map from `C[v]` has kernel `(v)` because `C` embeds
in `R_f`. Thus the strict transform is scheme-theoretically `V(v)`.
6. By `prop-nagata-proj-standard-open` and `def-nagata-affine-proj`, the overlap with
the parameter chart is `D(v)`: the actual homogeneous ratio is `(tz)/(fz) = t/f`.
7. The charts cover, so their complements glue to precisely the parameter chart, over
`Spec R[t]`. Finally `J/t` generates the same subalgebra as the fractions `f/t` for `f ∈ I`,
since `(f+tg)/t = f/t+g`.
-/
theorem affine_blowup_complement (I : Ideal R) (m : ℕ) (f : Fin m → I)
    (hf : Ideal.span (Set.range fun i ↦ (f i : R)) = I) :
    ∃ e : AffineBlowup (centerIdeal I) ≅ (center I).blowup,
      e.hom ≫ (center I).blowupMap = AffineBlowup.toSpec (centerIdeal I) ∧
      ∃ jt : Spec (.of (AffineBlowup.chartRing (centerIdeal I) Polynomial.X)) ⟶
          (center I).blowup,
        jt = AffineBlowup.chartRingιOfEq (centerIdeal I) (parameter I).2 rfl
            (reesX_mem _ _ (parameter I).2) ≫ e.hom ∧
        (transformIdeal I).comap jt = ⊤ ∧
        (∀ i : Fin m,
          ∃ θ : Polynomial (AffineBlowup.chartRing I (f i : R)) ≃+*
              AffineBlowup.chartRing (centerIdeal I) (Polynomial.C (f i : R)),
            (∀ c : AffineBlowup.chartRing I (f i : R),
              (θ (Polynomial.C c) : Localization.Away (Polynomial.C (f i : R))) =
                Localization.awayMap Polynomial.C (f i : R) c.val) ∧
            (θ Polynomial.X : Localization.Away (Polynomial.C (f i : R))) =
              AffineBlowup.chartFraction (Polynomial.C (f i : R)) 1 Polynomial.X ∧
            ∃ ji : Spec (.of (Polynomial (AffineBlowup.chartRing I (f i : R)))) ⟶
                (center I).blowup,
              ji = Spec.map (CommRingCat.ofHom θ.symm.toRingHom) ≫
                AffineBlowup.chartRingιOfEq (centerIdeal I) (constant I (f i)).2 rfl
                  (reesX_mem _ _ (constant I (f i)).2) ≫ e.hom ∧
              (transformIdeal I).comap ji =
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
                  (Ideal.span {Polynomial.X} :
                    Ideal (Polynomial (AffineBlowup.chartRing I (f i : R))))))).ker ∧
              ji ⁻¹' Set.range jt =
                {p | Polynomial.X ∉ p.asIdeal} ∧
              ji ⁻¹' ((transformIdeal I).support : Set (center I).blowup)ᶜ =
                ji ⁻¹' Set.range jt) ∧
        Set.range jt = ((transformIdeal I).support : Set (center I).blowup)ᶜ ∧
        (∃ c : Spec (.of (AffineBlowup.chartRing (centerIdeal I) Polynomial.X)) ≅
            Scheme.Opens.toScheme ((transformIdeal I).support.compl),
          c.hom ≫ Scheme.Opens.ι ((transformIdeal I).support.compl) = jt ∧
          c.hom ≫ Scheme.Opens.ι ((transformIdeal I).support.compl) ≫ (center I).blowupMap =
            Spec.map (CommRingCat.ofHom (algebraMap (Polynomial R)
              (AffineBlowup.chartRing (centerIdeal I) Polynomial.X)))) ∧
        AffineBlowup.chartRing (centerIdeal I) Polynomial.X =
          Algebra.adjoin (Polynomial R)
            (Set.range fun a : I ↦
              AffineBlowup.chartFraction (Polynomial.X : Polynomial R) 1
                (Polynomial.C (a : R))) := by
  classical
  obtain ⟨e, he⟩ := exists_affine_comparison I
  let jt := AffineBlowup.chartRingι (centerIdeal I) (parameter I).2 ≫ e.hom
  have ht : (transformIdeal I).comap jt = ⊤ := parameter_transformIdeal I e he
  choose θ hC hX using fun i : Fin m ↦ exists_constant_chart I (f i : R)
  let ji (i : Fin m) := Spec.map (CommRingCat.ofHom (θ i).symm.toRingHom) ≫
    AffineBlowup.chartRingι (centerIdeal I) (constant I (f i)).2 ≫ e.hom
  have hk (i : Fin m) := constant_transformIdeal I (f i) e he (θ i) (hC i) (hX i)
  have ho (i : Fin m) : ji i ⁻¹' Set.range jt =
      {p | Polynomial.X ∉ p.asIdeal} := constant_chart_overlap I (f i) e (θ i) (hX i)
  have hl (i : Fin m) :
      ji i ⁻¹' ((transformIdeal I).support : Set (center I).blowup)ᶜ =
        ji i ⁻¹' Set.range jt := by
    have hs : ji i ⁻¹' ((transformIdeal I).support : Set (center I).blowup) =
        {p | Polynomial.X ∈ p.asIdeal} := by
      have h := congrArg (fun J : (Spec (.of
        (Polynomial (AffineBlowup.chartRing I (f i : R))))).IdealSheafData ↦
          (J.support : Set (Spec (.of
            (Polynomial (AffineBlowup.chartRing I (f i : R))))))) (hk i)
      simpa only [Scheme.IdealSheafData.support_comap,
        TopologicalSpace.Closeds.coe_preimage, quotient_ker_support] using h
    rw [Set.preimage_compl, hs, ho]
    rfl
  have hsub : Set.range jt ⊆ ((transformIdeal I).support : Set (center I).blowup)ᶜ := by
    rintro _ ⟨q, rfl⟩
    have hs : (transformIdeal I).support.preimage jt.continuous = ⊥ := by
      rw [← Scheme.IdealSheafData.support_comap, ht, Scheme.IdealSheafData.support_top]
    intro hq
    have : q ∈ (transformIdeal I).support.preimage jt.continuous := hq
    rw [hs] at this
    exact this
  have hr : Set.range jt = ((transformIdeal I).support : Set (center I).blowup)ᶜ := by
    refine Set.Subset.antisymm hsub ?_
    intro y hy
    have hey : e.hom (e.inv y) = y := by
      change (e.inv ≫ e.hom) y = y
      rw [e.inv_hom_id]
      rfl
    rcases chart_cover I m f hf (e.inv y) with hp | ⟨i, hp⟩
    · obtain ⟨q, hq⟩ := Scheme.Hom.mem_opensRange.mp hp
      exact ⟨q, by
        change e.hom (AffineBlowup.chartRingι (centerIdeal I) (parameter I).2 q) = y
        rw [hq]
        exact hey⟩
    · obtain ⟨q, hq⟩ := Scheme.Hom.mem_opensRange.mp hp
      have : IsIso (CommRingCat.ofHom (θ i).symm.toRingHom) :=
        (θ i).symm.toCommRingCatIso.isIso_hom
      obtain ⟨q', hq'⟩ :=
        (Spec.map (CommRingCat.ofHom (θ i).symm.toRingHom)).homeomorph.surjective q
      have hji : ji i q' = y := by
        change e.hom (AffineBlowup.chartRingι (centerIdeal I)
          (constant I (f i)).2 ((Spec.map (CommRingCat.ofHom (θ i).symm.toRingHom)) q')) = y
        rw [show (Spec.map (CommRingCat.ofHom (θ i).symm.toRingHom)) q' = q from hq', hq]
        exact hey
      have hqcomp : q' ∈ ji i ⁻¹'
          ((transformIdeal I).support : Set (center I).blowup)ᶜ := by
        change ji i q' ∈ ((transformIdeal I).support : Set (center I).blowup)ᶜ
        rwa [hji]
      rw [hl] at hqcomp
      change ji i q' ∈ Set.range jt at hqcomp
      rwa [hji] at hqcomp
  refine ⟨e, he, jt, rfl, ht, ?_, hr, ?_, chartRing_parameter I⟩
  · intro i
    exact ⟨θ i, hC i, hX i, ji i, rfl, hk i, ho i, hl i⟩
  · have hopen : jt.opensRange = (transformIdeal I).support.compl := by
      apply SetLike.coe_injective
      exact hr
    let c := jt.isoOpensRange ≪≫ Scheme.isoOfEq _ hopen
    have hc : c.hom ≫ Scheme.Opens.ι ((transformIdeal I).support.compl) = jt := by
      dsimp [c]
      rw [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoOpensRange_hom_ι]
    refine ⟨c, hc, ?_⟩
    rw [← Category.assoc, hc]
    dsimp [jt]
    rw [Category.assoc, he]
    exact AffineBlowup.chartRingιOfEq_toSpec _ _ rfl _

end AlgebraicGeometry.DncAffineBlowup
