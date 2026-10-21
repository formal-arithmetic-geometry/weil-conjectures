/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A normalization model ready for purity after the group-order root extension
Source: Stacks Project, Tags 09EB, 0BRM, 0EYG and 0EYH.
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- Transfer the retained upstream theorem through the canonical small-colimit comparison.
private theorem small_regular_divisor_quotient
    (R : CommRingCat.{u}) [IsRegularRing R] (f : R)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY)
    (hg : ¬ IsUnit (b.hom f)) :
    IsNoetherianRing (strictHenselizationRing barY) ∧
      IsRegularRing (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) ∧
      IsDomain (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) := by
  let e : strictHenselizationRing barY ≅ strictHenselization barY :=
    smallStrictHenselizationColimitIso barY
  have hbe : Spec.map (b ≫ e.hom) = strictLocalizationToBase barY := by
    rw [Spec.map_comp, hb, ← smallStrictHenselizationColimitIso_toBase barY]
    simp only [e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  have hg' : ¬ IsUnit ((b ≫ e.hom).hom f) := by
    intro h
    apply hg
    have h' := h.map e.inv.hom
    change IsUnit (e.commRingCatIsoToRingEquiv.symm
      (e.commRingCatIsoToRingEquiv (b.hom f))) at h'
    simpa only [RingEquiv.symm_apply_apply] using h'
  obtain ⟨hN, hQ, hD⟩ :=
    strictHenselization_regular_divisor_quotient R f barY (b ≫ e.hom) hbe hg'
  let : IsNoetherianRing (strictHenselization barY) := hN
  let : IsRegularRing
      (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}) := hQ
  let eQ : (strictHenselization barY ⧸ Ideal.span {(b ≫ e.hom).hom f}) ≃+*
      (strictHenselizationRing barY ⧸ Ideal.span {b.hom f}) :=
    Ideal.quotientEquiv _ _ e.symm.commRingCatIsoToRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton]
      change Ideal.span {b.hom f} = Ideal.span {
        e.commRingCatIsoToRingEquiv.symm (e.commRingCatIsoToRingEquiv (b.hom f))}
      rw [RingEquiv.symm_apply_apply])
  exact ⟨isNoetherianRing_of_ringEquiv _ e.symm.commRingCatIsoToRingEquiv,
    IsRegularRing.of_ringEquiv eQ, eQ.toMulEquiv.isDomain_iff.mp hD⟩


-- The identity affine chart gives the prescribed small-ring algebra as an ind-etale colimit.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem purityData_small_strictHenselization_flat
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    RingHom.Flat b.hom := by
  let : Algebra R (strictHenselizationRing barY) := b.hom.toAlgebra
  have he : Algebra.IndEtale R (strictHenselizationRing barY) :=
    smallStrictHenselization_indEtale_of_affine_chart
      (A := strictHenselizationRing barY) barY R (𝟙 _)
      ⟨barY (IsLocalRing.closedPoint Ω), rfl⟩ (Iso.refl _) b.hom
      (by
        change Spec.map b ≫ 𝟙 _ = 𝟙 _ ≫ strictHenselizationStructuralMap barY
        simpa only [Category.comp_id, Category.id_comp] using hb)
  obtain ⟨J, _, _, P, hP⟩ := he.exists_colimitPresentation
  exact ModuleCat.flat_of_colimitPresentation
    (P.map (forget₂ _ (AlgCat R) ⋙ forget₂ _ (ModuleCat R))) fun j ↦ by
      change Module.Flat R (P.diag.obj j)
      have := hP j
      infer_instance

-- Transfer the upstream model through the canonical isomorphism of root algebras.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem small_root_tame_normalization
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    let H := strictHenselizationRing barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g → IsLocallyNoetherian N →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∃ (C : Scheme.{u}) (n : C ⟶ N),
        IsFinite n ∧ Etale (n ∣_ V) ∧
        ∃ (O : N.Opens), j η ∈ O ∧ Etale (n ∣_ O) ∧
        ∃ ζ : (n ⁻¹ᵁ V).toScheme ≅
            pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
          ζ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
            n ∣_ V := by
  classical
  dsimp only
  intro hg hN D j hD hDi hj hV η hη
  let H := strictHenselizationRing barY
  let g := b.hom f
  let P := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
  let A := AdjoinRoot P
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  let e : strictHenselizationRing barY ≅ strictHenselization barY :=
    smallStrictHenselizationColimitIso barY
  let b' := b ≫ e.hom
  have hb' : Spec.map b' = strictLocalizationToBase barY := by
    rw [Spec.map_comp, hb, ← smallStrictHenselizationColimitIso_toBase barY]
    simp only [e, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.id_comp]
  let H' := strictHenselization barY
  let g' := b'.hom f
  let P' := (Polynomial.X : Polynomial H') ^ Nat.card G - Polynomial.C g'
  let A' := AdjoinRoot P'
  let N' := Spec (CommRingCat.of A')
  let q' := Spec.map (CommRingCat.ofHom (algebraMap H' A'))
  let V' : N'.Opens := PrimeSpectrum.basicOpen (algebraMap H' A' g')
  let eR : H ≃+* H' := e.commRingCatIsoToRingEquiv
  have hP : P.map eR = P' := by
    simp only [P, P', Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X]
    rw [Polynomial.map_C (f := (eR : H →+* H'))]
    rfl
  let eA : A ≃+* A' := AdjoinRoot.mapRingEquiv eR P P' (Associated.of_eq hP)
  have heA (x : H) : eA (AdjoinRoot.of P x) = AdjoinRoot.of P' (e.hom x) := by
    exact AdjoinRoot.map_of eR P P' (Associated.of_eq hP).symm.dvd x
  let t : N' ⟶ N := Spec.map eA.toCommRingCatIso.hom
  have : IsIso t := inferInstance
  have hv : t ⁻¹ᵁ V = V' := by
    change PrimeSpectrum.basicOpen (eA (AdjoinRoot.of P g)) =
      PrimeSpectrum.basicOpen (AdjoinRoot.of P' g')
    exact congrArg PrimeSpectrum.basicOpen (heA g)
  let v : V'.toScheme ≅ V.toScheme := N'.isoOfEq hv.symm ≪≫ t.preimageIso V
  have hvι : v.hom ≫ V.ι = V'.ι ≫ t := by
    simp only [v, Iso.trans_hom, Category.assoc, Scheme.Hom.preimageIso_hom_ι,
      Scheme.isoOfEq_hom_ι_assoc]
  have hq : t ≫ q ≫ Spec.map b = q' ≫ Spec.map b' := by
    simp only [t, q, q', ← Spec.map_comp]
    congr 1
    ext x
    exact heA (b.hom x)
  have hg' : ¬ IsUnit g' := by
    intro h
    apply hg
    have h' := h.map e.inv.hom
    change IsUnit (e.commRingCatIsoToRingEquiv.symm
      (e.commRingCatIsoToRingEquiv g)) at h'
    simpa only [RingEquiv.symm_apply_apply] using h'
  have : IsLocallyNoetherian N := hN
  have hN' : IsLocallyNoetherian N' :=
    isLocallyNoetherian_of_isOpenImmersion t
  let j' := j ≫ inv t
  have hj' : IsEffectiveCartierCenter j' := by
    have : IsClosedImmersion j := hj.isClosedImmersion
    have : IsClosedImmersion j' := inferInstance
    let d : D ⟶ pullback t j := pullback.lift j' (𝟙 D) (by simp [j'])
    have hd : d ≫ pullback.snd t j = 𝟙 D := pullback.lift_snd _ _ _
    have : IsIso d := by
      have : IsIso (d ≫ pullback.snd t j) := hd ▸ inferInstance
      exact IsIso.of_isIso_comp_right d (pullback.snd t j)
    apply isEffectiveCartierCenter_iff_isInvertible_ker.mpr
    have hd' : d ≫ pullback.fst t j = j' := pullback.lift_fst _ _ _
    rw [← hd', Hom.ker_comp_of_isIso,
      IdealSheafData.ker_fst_of_isClosedImmersion]
    exact (isEffectiveCartierCenter_iff_isInvertible_ker.mp hj).comap_of_flat t
  have hV' (z : N') : z ∈ V' ↔ z ∉ Set.range j' := by
    rw [← hv]
    change t z ∈ V ↔ _
    rw [hV]
    apply not_congr
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, ?_⟩
      change inv t (j d) = z
      rw [hd]
      exact t.homeomorph.symm_apply_apply z
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      change j d = t (inv t (j d))
      exact (t.homeomorph.apply_symm_apply (j d)).symm
  obtain ⟨C, n, hn, hnV, O, hO, hnO, ζ, hζ⟩ :=
    W.strict_hensel_root_tame_normalization i G R φ f hG hf β hβ barY b' hb'
      hg' hN' D j' hD hDi hj' hV' η hη
  have : IsFinite n := hn
  let n₀ := n ≫ t
  let O₀ := inv t ⁻¹ᵁ O
  have htO : t ⁻¹ᵁ O₀ = O := by
    simp only [O₀, ← Scheme.Hom.comp_preimage, IsIso.hom_inv_id, Scheme.Hom.id_preimage]
  have hn₀V : Etale (n₀ ∣_ V) := by
    dsimp only [n₀]
    rw [morphismRestrict_comp]
    have hnV' : Etale (n ∣_ t ⁻¹ᵁ V) :=
      (MorphismProperty.arrow_mk_iso_iff (P := @Etale) (morphismRestrictEq n hv)).mpr hnV
    have := hnV'
    infer_instance
  have hn₀O : Etale (n₀ ∣_ O₀) := by
    dsimp only [n₀]
    rw [morphismRestrict_comp]
    have hnO' : Etale (n ∣_ t ⁻¹ᵁ O₀) :=
      (MorphismProperty.arrow_mk_iso_iff (P := @Etale) (morphismRestrictEq n htO)).mpr hnO
    have := hnO'
    infer_instance
  have hO₀ : j η ∈ O₀ := hO
  let ψ := V.ι ≫ q ≫ Spec.map b ≫ φ
  let ψ' := V'.ι ≫ q' ≫ Spec.map b' ≫ φ
  have hvψ : v.hom ≫ ψ = ψ' := by
    calc
      v.hom ≫ ψ = (v.hom ≫ V.ι) ≫ q ≫ Spec.map b ≫ φ := by
        simp only [ψ, Category.assoc]
      _ = (V'.ι ≫ t) ≫ q ≫ Spec.map b ≫ φ := by rw [hvι]
      _ = ψ' := by
        simpa only [ψ', Category.assoc] using
          congrArg (fun a ↦ V'.ι ≫ a ≫ φ) hq
  let k := pullback.map (W.π ≫ i) ψ' (W.π ≫ i) ψ
    (𝟙 _) v.hom (𝟙 _) (by simp) (by simpa using hvψ.symm)
  have : IsIso k := inferInstance
  have hs : n₀ ⁻¹ᵁ V = n ⁻¹ᵁ V' := by
    simp only [n₀, Scheme.Hom.comp_preimage, hv]
  let ζ₀ := C.isoOfEq hs ≪≫ ζ ≪≫ asIso k
  have hζ₀ : ζ₀.hom ≫ pullback.snd (W.π ≫ i) ψ = n₀ ∣_ V := by
    apply (cancel_mono V.ι).mp
    have hk : k ≫ pullback.snd (W.π ≫ i) ψ =
        pullback.snd (W.π ≫ i) ψ' ≫ v.hom := pullback.lift_snd _ _ _
    calc
      ζ₀.hom ≫ pullback.snd (W.π ≫ i) ψ ≫ V.ι =
          (C.isoOfEq hs).hom ≫ ζ.hom ≫
            pullback.snd (W.π ≫ i) ψ' ≫ v.hom ≫ V.ι := by
        simp only [ζ₀, Iso.trans_hom, asIso_hom, Category.assoc]
        rw [reassoc_of% hk]
      _ = (C.isoOfEq hs).hom ≫ (n ∣_ V') ≫ V'.ι ≫ t := by
        rw [hvι, reassoc_of% hζ]
      _ = (n₀ ⁻¹ᵁ V).ι ≫ n₀ := by
        simp only [morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc, n₀]
      _ = (n₀ ∣_ V) ≫ V.ι := (morphismRestrict_ι n₀ V).symm
  exact ⟨C, n₀, inferInstance, hn₀V, O₀, hO₀, hn₀O, ζ₀, hζ₀⟩

private theorem root_pow (R : Type u) [CommRing R] (f : R) (n : ℕ) :
    AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f) ^ n =
      AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f) f := by
  have h := AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f)
  simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero] using h

set_option backward.isDefEq.respectTransparency false in
private noncomputable def root_quotient_equiv (R : Type u) [CommRing R]
    (f : R) (n : ℕ) (hn : 0 < n) :
    (AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f) ⧸
      Ideal.span {AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f)}) ≃+*
      (R ⧸ Ideal.span {f}) := by
  let P := (Polynomial.X : Polynomial R) ^ n - Polynomial.C f
  let B := AdjoinRoot P
  let t := AdjoinRoot.root P
  let I := Ideal.span ({t} : Set B)
  let J := Ideal.span ({f} : Set R)
  let v := AdjoinRoot.lift (f := P) (Ideal.Quotient.mk J) 0 (by
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, zero_pow hn.ne', zero_sub, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f))
  let g : B ⧸ I →+* R ⧸ J := Ideal.Quotient.lift I v (by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy
    rw [map_mul]
    have hv : v t = 0 := AdjoinRoot.lift_root _
    rw [hv, zero_mul])
  let w := (Ideal.Quotient.mk I).comp (AdjoinRoot.of P)
  have hw : w f = 0 := by
    change Ideal.Quotient.mk I (AdjoinRoot.of P f) = 0
    rw [← root_pow R f n, map_pow]
    have ht : Ideal.Quotient.mk I t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    change (Ideal.Quotient.mk I t) ^ n = 0
    rw [ht, zero_pow hn.ne']
  let h : R ⧸ J →+* B ⧸ I := Ideal.Quotient.lift J w (by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy
    rw [map_mul, hw, zero_mul])
  apply RingEquiv.ofRingHom g h
  · apply Ideal.Quotient.ringHom_ext
    ext r
    change v (AdjoinRoot.of P r) = Ideal.Quotient.mk J r
    exact AdjoinRoot.lift_of _
  · apply Ideal.Quotient.ringHom_ext
    apply AdjoinRoot.ringHom_ext
    · ext r
      change h (g (Ideal.Quotient.mk I (AdjoinRoot.of P r))) =
        Ideal.Quotient.mk I (AdjoinRoot.of P r)
      change h (v (AdjoinRoot.of P r)) = _
      rw [show v (AdjoinRoot.of P r) = Ideal.Quotient.mk J r from AdjoinRoot.lift_of _]
      rfl
    · change h (g (Ideal.Quotient.mk I t)) = Ideal.Quotient.mk I t
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)]
      rw [map_zero, map_zero]


/-- A finite normalization model is etale at the generic point of the root divisor.
Source: Stacks Project, Tags 09EB, 0BRM, 0EYG and 0EYH, through the construction
of B' and tame normalization.
(blueprint: lem-sbc-strict-hensel-root-purity-data)

Proof: Identify the torsor over D(f) using beta, then base change it to H. The
canonical pointed-neighbourhood colimit is the strict henselization of the local
ring at barY. Flatness keeps g regular; quotient compatibility identifies H/(g)
with the strict henselization of the regular divisor local ring. For nonunit g,
H is regular local and H/(g) is a regular local domain. The monic root algebra
A is finite local over H, its root t is regular, and A/(t) is H/(g); hence A is
regular local. Put D=Spec(A/(t)), with its quotient closed immersion j. Since
t^n=g, its complement is V=D(g). In particular D is integral and regular,
j is an effective Cartier centre, and N is locally Noetherian.

At the generic point of D the local ring is a DVR. Each connected generic
component of the pulled-back torsor has Galois group a stabilizer in G. The
Galois degree formula 09EB makes its ramification and residue degrees divide
|G|, which is invertible, so its ramification is tame. The n-th root extension
has ramification index n there; Abhyankar 0BRM kills every component index.
Normalize N in the finite etale cover of V, taking the disjoint union over
its finitely many generic components. Tame normalization is finite (the
finite locally free tame normalization theorem 0EYH), and agrees with the cover on V by
normality. Its localization over the divisor generic point is finite etale
by Abhyankar. Etaleness is open for this finite presentation, giving O.
The agreement over V gives ζ and its projection identity. This lemma only
constructs the finite model: purity and surjectivity are proved separately.
The nonunit condition excludes the empty divisor; n>0 since G is a group. -/
theorem GaloisCover.strict_hensel_root_purity_data
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    let H := strictHenselizationRing barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g →
    IsLocallyNoetherian N ∧
      ∃ (D : Scheme.{u}) (j : D ⟶ N),
        IsRegular D ∧ IsIntegral D ∧ IsEffectiveCartierCenter j ∧
        (∀ z : N, z ∈ V ↔ z ∉ Set.range j) ∧
        ∃ (C : Scheme.{u}) (n : C ⟶ N),
          IsFinite n ∧ Etale (n ∣_ V) ∧
          ∃ (O : N.Opens) (η : D), IsGenericPoint η Set.univ ∧
            j η ∈ O ∧ Etale (n ∣_ O) ∧
          ∃ ζ : (n ⁻¹ᵁ V).toScheme ≅
              pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
            ζ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
              n ∣_ V := by
  classical
  dsimp only
  let H := strictHenselizationRing barY
  let g := b.hom f
  let P := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
  let A := AdjoinRoot P
  let t := AdjoinRoot.root P
  let I := Ideal.span ({t} : Set A)
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  intro hg
  obtain ⟨hH, hQ, hQD⟩ := small_regular_divisor_quotient R f barY b hb hg
  let : IsNoetherianRing H := hH
  let : IsRegularRing (H ⧸ Ideal.span {g}) := hQ
  let : IsDomain (H ⧸ Ideal.span {g}) := hQD
  have hm : P.Monic := Polynomial.monic_X_pow_sub_C g (Nat.card_pos (α := G)).ne'
  let : Module.Finite H A := hm.finite_adjoinRoot
  let : Module.Free H A := hm.free_adjoinRoot
  have hflat := purityData_small_strictHenselization_flat R barY b hb
  let : Algebra R H := b.hom.toAlgebra
  let : Module.Flat R H := hflat
  have hgH : IsSMulRegular H g := hf.of_flat
  have htreg : IsSMulRegular A t := by
    apply (IsSMulRegular.pow_iff (Nat.card_pos (α := G))).mp
    rw [root_pow H g (Nat.card G)]
    exact hgH.of_flat
  have htr : _root_.IsRegular t :=
    (Commute.isRegular_iff (fun a ↦ Commute.all _ a)).mpr
      (isLeftRegular_iff.mpr htreg)
  let e := root_quotient_equiv H g (Nat.card G) (Nat.card_pos (α := G))
  let : IsRegularRing (A ⧸ I) := IsRegularRing.of_ringEquiv e.symm
  let : IsDomain (A ⧸ I) := e.toMulEquiv.isDomain_iff.mpr hQD
  let D := Spec (CommRingCat.of (A ⧸ I))
  let j : D ⟶ N := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hD : IsRegular D := by
    constructor
    intro x
    exact IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (CommRingCat.of (A ⧸ I)) x).commRingCatIsoToRingEquiv.symm
  have hDI : IsIntegral D := inferInstance
  have hj : IsEffectiveCartierCenter j := by
    have : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective
    apply isEffectiveCartierCenter_iff_isInvertible_ker.mpr
    apply Scheme.IdealSheafData.IsInvertible.of_isAffine
    rw [Scheme.Hom.ker_apply]
    change (RingHom.ker j.appTop.hom).IsRegularPrincipal
    have hk : RingHom.ker j.appTop.hom =
        I.comap (ΓSpecIso (CommRingCat.of A)).hom.hom := by
      ext s
      rw [RingHom.mem_ker, Ideal.mem_comap]
      have hh := congrArg (fun k ↦ k s)
        (ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      change (ΓSpecIso (CommRingCat.of (A ⧸ I))).hom (j.appTop s) =
        Ideal.Quotient.mk I ((ΓSpecIso (CommRingCat.of A)).hom s) at hh
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hh]
      exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
        (ΓSpecIso (CommRingCat.of (A ⧸ I))).hom).1).symm
    rw [hk]
    exact (Ideal.isRegularPrincipal_span_singleton_of_isRegular htr).comap_of_bijective
      (ConcreteCategory.bijective_of_isIso _)
  have hV : ∀ z : N, z ∈ V ↔ z ∉ Set.range j := by
    intro z
    change algebraMap H A g ∉ z.asIdeal ↔
      z ∉ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
    change algebraMap H A g ∉ z.asIdeal ↔ ¬ ({t} : Set A) ⊆ z.asIdeal
    have htg : t ^ Nat.card G = algebraMap H A g := root_pow H g (Nat.card G)
    rw [Set.singleton_subset_iff, ← htg]
    exact not_congr (z.isPrime.pow_mem_iff_mem (Nat.card G) (Nat.card_pos (α := G)))
  have hN : IsLocallyNoetherian N := inferInstance
  let : IsIntegral D := hDI
  let η := genericPoint D
  have hη : IsGenericPoint η Set.univ := genericPoint_spec D
  obtain ⟨C, n, hn, hnV, O, hO, hnO, ζ, hζ⟩ :=
    small_root_tame_normalization i G W R φ f hG hf β hβ barY b hb
      hg hN D j hD hDI hj hV η hη
  exact ⟨hN, D, j, hD, hDI, hj, hV, C, n, hn, hnV, O, η, hη, hO, hnO, ζ, hζ⟩

end AlgebraicGeometry.Scheme

