/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData
import Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison
import Sheaf.AlgebraicGeometry.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProEtale.FaithfullyFlat
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularIntegralDivisorEtalePurity
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

/-! # The finite étale model after adjoining the group-order root

Source: Stacks Project, Tags 09EB, 0BRM, 0EYE and 0EYG.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- The upstream purity model transports along the canonical comparison of root algebras.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem small_root_purity_data
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
  intro hg
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
  obtain ⟨hN', D, j, hD, hDI, hj, hV', C, n, hn, hnV, O, η, hη, hO,
      hnO, ζ, hζ⟩ :=
    W.strict_hensel_root_purity_data i G R φ f hG hf β hβ barY b' hb' hg'
  have : IsLocallyNoetherian N' := hN'
  have hN : IsLocallyNoetherian N := isLocallyNoetherian_of_isOpenImmersion (inv t)
  let j₀ := j ≫ t
  have hj₀ : IsEffectiveCartierCenter j₀ := by
    have : IsClosedImmersion j := hj.isClosedImmersion
    have : IsClosedImmersion j₀ := inferInstance
    let d : D ⟶ pullback (inv t) j := pullback.lift j₀ (𝟙 D) (by simp [j₀])
    have hd : d ≫ pullback.snd (inv t) j = 𝟙 D := pullback.lift_snd _ _ _
    have : IsIso d := by
      have : IsIso (d ≫ pullback.snd (inv t) j) := hd ▸ inferInstance
      exact IsIso.of_isIso_comp_right d (pullback.snd (inv t) j)
    apply isEffectiveCartierCenter_iff_isInvertible_ker.mpr
    have hd' : d ≫ pullback.fst (inv t) j = j₀ := pullback.lift_fst _ _ _
    rw [← hd', Hom.ker_comp_of_isIso,
      IdealSheafData.ker_fst_of_isClosedImmersion]
    exact (isEffectiveCartierCenter_iff_isInvertible_ker.mp hj).comap_of_flat (inv t)
  have hV₀ (z : N) : z ∈ V ↔ z ∉ Set.range j₀ := by
    have hh : inv t z ∈ V' ↔ inv t z ∉ Set.range j := hV' (inv t z)
    rw [← hv] at hh
    change t (inv t z) ∈ V ↔ _ at hh
    rw [show t (inv t z) = z from t.homeomorph.apply_symm_apply z] at hh
    rw [hh]
    apply not_congr
    constructor
    · rintro ⟨d, hd⟩
      refine ⟨d, ?_⟩
      change t (j d) = z
      rw [hd]
      exact t.homeomorph.apply_symm_apply z
    · rintro ⟨d, rfl⟩
      refine ⟨d, ?_⟩
      change j d = inv t (t (j d))
      exact (t.homeomorph.symm_apply_apply (j d)).symm
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
  have hO₀ : j₀ η ∈ O₀ := by
    change inv t (t (j η)) ∈ O
    simpa only [show inv t (t (j η)) = j η from
      t.homeomorph.symm_apply_apply (j η)] using hO
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
  exact ⟨hN, D, j₀, hD, hDI, hj₀, hV₀, C, n₀, inferInstance, hn₀V,
    O₀, η, hη, hO₀, hn₀O, ζ₀, hζ₀⟩

-- Use the prescribed algebra structure in the identity affine chart. The existing
-- ind-etale presentation then supplies a filtered colimit of flat modules.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteEtaleModel_small_strictHenselization_flat
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

private theorem cover_pullback_properties
    {L U T : Scheme.{u}} (i : U ⟶ L)
    {G : Type (u + 1)} [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (t : T ⟶ Spec R) (ht : Set.range t ⊆ (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum R))) :
    IsFinite (pullback.snd (W.π ≫ i) (t ≫ φ)) ∧
      Etale (pullback.snd (W.π ≫ i) (t ≫ φ)) ∧
      Surjective (pullback.snd (W.π ≫ i) (t ≫ φ)) := by
  have : IsOpenImmersion (pullback.snd i φ) := by
    rw [← hβ]
    infer_instance
  have hr : Set.range (pullback.snd i φ) =
      (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum R)) := by
    rw [← hβ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr β.hom.surjective, Set.image_univ, Scheme.Opens.range_ι]
  have hs : Surjective (pullback.snd (pullback.snd i φ) t) := by
    rw [surjective_iff, ← Set.range_eq_univ, IsOpenImmersion.range_pullbackSnd]
    change t ⁻¹' Set.range (pullback.snd i φ) = Set.univ
    rw [hr]
    exact Set.eq_univ_of_forall fun x ↦ ht ⟨x, rfl⟩
  have : IsIso (pullback.snd (pullback.snd i φ) t) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hs⟩
  have : IsIso (pullback.snd i (t ≫ φ)) := by
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd i φ t]
    infer_instance
  have : IsFinite W.π := W.isFinite
  have : Etale W.π := W.etale
  have : Surjective W.π := W.surjective
  let e := pullbackRightPullbackFstIso i (t ≫ φ) W.π
  have he : pullback.snd (W.π ≫ i) (t ≫ φ) =
      e.inv ≫ pullback.snd W.π (pullback.fst i (t ≫ φ)) ≫
        pullback.snd i (t ≫ φ) := by
    simp [e]
  rw [he]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The punctured root pullback extends as a surjective finite étale cover.

Source: Stacks Project, Tags 09EB, 0BRM, 0EYE and 0EYG, construction of C.
(blueprint: lem-sbc-strict-hensel-root-finite-etale-model)

Proof: Identify the pullback of U with D(f) using beta. The canonical ring H is
strictly henselian and flat over R; its regularity and the regularity of H/(g)
follow from strict henselization of the local rings of R and R/(f). Flatness keeps
g a nonzerodivisor. At each divisor generic point the ring is a DVR. The torsor's
connected generic components are Galois with stabilizer groups contained in G.
The degree formula 09EB makes their ramification indices divide |G|. Since |G|
is a unit, the extensions are tame, with separable residue extensions. When g
is nonunit, the root ring is local, its root is a nonzerodivisor, and its quotient
by that root is H/(g). It is regular by the regular quotient criterion. Abhyankar's
lemma 0BRM makes all ramification indices one after this root extension. Purity
0EYE then extends the punctured finite étale cover to a finite étale cover E of N.
The extension agrees with the original cover over V, giving delta and the displayed
projection equality. V is dense since g is a nonzerodivisor in the finite free
root ring. The image of E is closed (finiteness) and contains V (torsor surjectivity),
hence is N. When g is a unit V=N, so use the original pullback as E and its canonical
identification; no purity or locality of the root ring is needed in that case. -/
theorem GaloisCover.strict_hensel_root_finite_etale_model
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
    ∃ (E : Scheme.{u}) (p : E ⟶ N),
      IsFinite p ∧ Etale p ∧ Function.Surjective p ∧
      ∃ δ : pullback p V.ι ≅ pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
        δ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
          pullback.snd p V.ι := by
  dsimp only
  let H := strictHenselizationRing barY
  let g := b.hom f
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
  let N := Spec (CommRingCat.of A)
  let q : N ⟶ Spec H := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  let t := V.ι ≫ q ≫ Spec.map b
  let r := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
  have ht : Set.range t ⊆ (↑(PrimeSpectrum.basicOpen f) : Set (PrimeSpectrum R)) := by
    rintro _ ⟨x, rfl⟩
    change algebraMap H A (b.hom f) ∉ (V.ι x).asIdeal
    exact x.2
  have hpull := cover_pullback_properties i W R φ f β hβ t ht
  have hprops : IsFinite r ∧ Etale r ∧ Surjective r := by
    have hcomp : t ≫ φ = V.ι ≫ q ≫ Spec.map b ≫ φ := by
      simp only [t, Category.assoc]
    rw [hcomp] at hpull
    exact hpull
  obtain ⟨hrfin, hret, hrsurj⟩ := hprops
  have hr : Surjective r := hrsurj
  by_cases hg : IsUnit g
  · have hV : V = ⊤ := by
      change PrimeSpectrum.basicOpen (algebraMap H A g) = ⊤
      ext x
      change (algebraMap H A g ∉ x.asIdeal) ↔ True
      exact iff_true_intro (x.asIdeal.notMem_of_isUnit (hg.map (algebraMap H A)))
    have : IsIso V.ι := isIso_of_isOpenImmersion_of_opensRange_eq_top V.ι (by
      simpa only [Scheme.Opens.opensRange_ι] using hV)
    have : IsFinite r := hrfin
    have : Etale r := hret
    let p := r ≫ V.ι
    let e := asIso (pullback.fst p V.ι)
    refine ⟨_, p, inferInstance, inferInstance, ?_, e, ?_⟩
    · exact (inferInstance : Surjective p).surj
    · change pullback.fst p V.ι ≫ r = pullback.snd p V.ι
      apply (cancel_mono V.ι).mp
      simpa only [Category.assoc] using (pullback.condition (f := p) (g := V.ι))
  · obtain ⟨hN, D, j, hD, hDI, hj, hV, C, n, hn, hnV, O, η, hη, hO, hnO, ζ, hζ⟩ :=
      small_root_purity_data i G W R φ f hG hf β hβ barY b hb hg
    have : IsLocallyNoetherian N := hN
    have : IsRegular D := hD
    have : IsIntegral D := hDI
    have : IsFinite n := hn
    have hηeq : η = genericPoint D := hη.eq (genericPoint_spec D)
    have hO' : j (genericPoint D) ∈ O := by
      simpa only [hηeq] using hO
    obtain ⟨E, p, hpfin, hpet, e, he⟩ :=
      exists_finite_etale_extension_of_regular_integral_divisor j hj V hV n hnV O hO' hnO
    have : IsFinite p := hpfin
    have : Etale p := hpet
    let δ := pullbackRestrictIsoRestrict p V ≪≫ e.symm ≪≫ ζ
    have hζ' : ζ.hom ≫ r = n ∣_ V := hζ
    have hδ : δ.hom ≫ r = pullback.snd p V.ι := by
      simp only [δ, Iso.trans_hom, Category.assoc, hζ']
      rw [← he, Iso.symm_hom, Iso.inv_hom_id_assoc,
        pullbackRestrictIsoRestrict_hom_morphismRestrict]
    have hflat := finiteEtaleModel_small_strictHenselization_flat R barY b hb
    let : Algebra R H := b.hom.toAlgebra
    have : Module.Flat R H := hflat
    have hgH : IsSMulRegular H g := hf.of_flat
    have : Module.Free H A :=
      (Polynomial.monic_X_pow_sub_C g (Nat.card_pos (α := G)).ne').free_adjoinRoot
    have hgA : IsSMulRegular A (algebraMap H A g) := hgH.of_flat
    have ha : _root_.IsRegular (algebraMap H A g) :=
      (Commute.isRegular_iff (fun a ↦ Commute.all _ a)).mpr
        (isLeftRegular_iff.mpr hgA)
    have hinj : Function.Injective
        (algebraMap A (Localization.Away (algebraMap H A g))) :=
      IsLocalization.injective (M := Submonoid.powers (algebraMap H A g))
        (Localization.Away (algebraMap H A g)) (by
          rintro a ⟨k, rfl⟩
          exact (ha.pow k).mem_nonZeroDivisors)
    have hdense : Dense (V : Set N) := by
      change Dense (↑(PrimeSpectrum.basicOpen (algebraMap H A g)) : Set (PrimeSpectrum A))
      rw [← PrimeSpectrum.localization_away_comap_range
        (Localization.Away (algebraMap H A g)) (algebraMap H A g)]
      apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr
      rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]
      exact bot_le
    have hrange : (V : Set N) ⊆ Set.range p := by
      intro x hx
      obtain ⟨y, hy⟩ := hr.surj ⟨x, hx⟩
      let z := δ.inv y
      refine ⟨pullback.fst p V.ι z, ?_⟩
      have hz : pullback.snd p V.ι z = ⟨x, hx⟩ := by
        have hh : δ.inv ≫ pullback.snd p V.ι = r := by
          rw [← hδ, Iso.inv_hom_id_assoc]
        have hv := congrArg (fun a ↦ a y) hh
        exact hv.trans hy
      have hp := congrArg (fun a ↦ a z) (pullback.condition (f := p) (g := V.ι))
      change p (pullback.fst p V.ι z) = (pullback.snd p V.ι z).val at hp
      exact hp.trans (congrArg Subtype.val hz)
    have hpclosed := p.isClosedMap.isClosed_range
    have hponto : Function.Surjective p := by
      rw [← Set.range_eq_univ, ← hpclosed.closure_eq]
      exact (hdense.mono hrange).closure_eq
    exact ⟨E, p, hpfin, hpet, hponto, δ, hδ⟩

end AlgebraicGeometry.Scheme
