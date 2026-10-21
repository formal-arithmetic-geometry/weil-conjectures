/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData
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
      W.strict_hensel_root_purity_data i G R φ f hG hf β hβ barY b hb hg
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
