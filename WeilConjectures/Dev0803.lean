/-
Development scratch for `exists_finiteDegree_center_le_blowup` (Stacks Tag 0803).
Contents are merged into `WeilConjectures.Compactification.Flattening` when done.
-/
module

public import WeilConjectures.Compactification.Flattening

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

section LocalAlgebra

open HomogeneousLocalization Polynomial

variable {A : Type u} [CommRing A] (I₀ : Ideal A)

/-- Every element of the chart ring of the affine blow-up is a chart fraction
`g/aⁿ` for some degree `n` and some `g ∈ I₀ ^ n`. -/
lemma AffineBlowup.chartFrac_surjective {a : A} (ha : a ∈ I₀)
    (x : HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ a ha)) :
    ∃ (n : ℕ) (g : A) (hg : g ∈ I₀ ^ n), AffineBlowup.chartFrac I₀ ha hg = x := by
  obtain ⟨n, s, hsmem, rfl⟩ :=
    HomogeneousLocalization.Away.mk_surjective (reesGrading I₀) (reesX_mem I₀ a ha) x
  have hs' : s ∈ reesGrading I₀ n := by simpa using hsmem
  obtain ⟨g, hg, hrepr⟩ := (mem_reesGrading_iff_exists I₀).mp hs'
  subst hrepr
  exact ⟨n, g, hg, rfl⟩

/-- Congruence for polynomial monomials with different indices. -/
private lemma monomial_congr {i j : ℕ} {c d : A} (hij : i = j) (hcd : c = d) :
    (Polynomial.monomial i) c = (Polynomial.monomial j) d := by
  subst hij; subst hcd; rfl

/-- Clearing a power of `a` from the numerator of a chart fraction on the `b`-chart:
`(aᵏ·x)/bᵏ⁺ⁿ = (a/b)ᵏ · (x/bⁿ)`, where `a/b` is the localization element of the chart
comparison. -/
lemma AffineBlowup.chartFrac_pow_mul {a b : A} (ha : a ∈ I₀) (hb : b ∈ I₀)
    {k n : ℕ} {x : A} (hx : x ∈ I₀ ^ n) (hax : a ^ k * x ∈ I₀ ^ (k + n)) :
    AffineBlowup.chartFrac I₀ hb hax =
      HomogeneousLocalization.Away.isLocalizationElem (reesX_mem I₀ b hb)
          (reesX_mem I₀ a ha) ^ k *
        AffineBlowup.chartFrac I₀ hb hx := by
  rw [AffineBlowup.chartFrac, AffineBlowup.chartFrac, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.isLocalizationElem,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [coe_reesMonomial, coe_reesX]
  simp only [Polynomial.monomial_pow, Polynomial.monomial_mul_monomial, one_mul, pow_one]
  exact monomial_congr (by ring) (by ring)

/-- Cancelling a power of `a` on its own chart: `(aᵏ·x)/aᵏ⁺ⁿ = x/aⁿ`. -/
lemma AffineBlowup.chartFrac_self_pow_mul {a : A} (ha : a ∈ I₀)
    {k n : ℕ} {x : A} (hx : x ∈ I₀ ^ n) (hax : a ^ k * x ∈ I₀ ^ (k + n)) :
    AffineBlowup.chartFrac I₀ ha hax = AffineBlowup.chartFrac I₀ ha hx := by
  rw [AffineBlowup.chartFrac, AffineBlowup.chartFrac, HomogeneousLocalization.ext_iff_val,
    HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  apply Subtype.ext
  push_cast [coe_reesMonomial, coe_reesX]
  simp only [Polynomial.monomial_pow, Polynomial.monomial_mul_monomial, one_mul]
  exact monomial_congr (by ring) (by ring)

/-- **The denominator-clearing lemma on two charts of the same Rees algebra**
(the algebraic core of Stacks Tag 0803), ring-level form: let `Ja`, `Jb` be ideals of
the `a`- and `b`-charts which agree in the common localization `B_{b·a}`. If the chart
fraction `g/aᵉ` lies in `Ja`, then multiplying `g/bᵉ` by any large enough power of the
localization element `a/b` lands in `Jb`. -/
lemma AffineBlowup.exists_isLocalizationElem_pow_mul_chartFrac_mem
    {a b : A} (ha : a ∈ I₀) (hb : b ∈ I₀)
    (Ja : Ideal (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ a ha)))
    (Jb : Ideal (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ b hb)))
    (hab : Ja.map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ b hb)
        (mul_comm (reesX I₀ b hb) (reesX I₀ a ha))) =
      Jb.map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
        (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha)))
    {e : ℕ} {g : A} (hg : g ∈ I₀ ^ e) (hμ : AffineBlowup.chartFrac I₀ ha hg ∈ Ja) :
    ∃ N : ℕ, ∀ N' ≥ N,
      HomogeneousLocalization.Away.isLocalizationElem (reesX_mem I₀ b hb)
          (reesX_mem I₀ a ha) ^ N' *
        AffineBlowup.chartFrac I₀ hb hg ∈ Jb := by
  set ρb := HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
    (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha) with hρb
  set t := HomogeneousLocalization.Away.isLocalizationElem
    (reesX_mem I₀ b hb) (reesX_mem I₀ a ha) with ht
  -- the image of `g/bᵉ` lies in the extension of `Jb` to the overlap
  have hmem : ρb (AffineBlowup.chartFrac I₀ hb hg) ∈ Jb.map ρb := by
    rw [hρb, AffineBlowup.awayMap_chartFrac I₀ hb ha hg, ← hab]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hμ)
  -- the overlap ring is the localization of the `b`-chart at `a/b`
  letI : Algebra
      (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ b hb))
      (HomogeneousLocalization.Away (reesGrading I₀)
        (reesX I₀ b hb * reesX I₀ a ha)) := ρb.toAlgebra
  haveI hloc : IsLocalization.Away t (HomogeneousLocalization.Away (reesGrading I₀)
      (reesX I₀ b hb * reesX I₀ a ha)) :=
    HomogeneousLocalization.Away.isLocalization_mul (reesX_mem I₀ b hb)
      (reesX_mem I₀ a ha) rfl one_ne_zero
  have halg : algebraMap
      (HomogeneousLocalization.Away (reesGrading I₀) (reesX I₀ b hb))
      (HomogeneousLocalization.Away (reesGrading I₀)
        (reesX I₀ b hb * reesX I₀ a ha)) = ρb :=
    RingHom.algebraMap_toAlgebra ρb
  obtain ⟨N, hN⟩ := Ideal.exists_pow_mul_mem_of_algebraMap_mem_map t
    (K := Jb) (x := AffineBlowup.chartFrac I₀ hb hg) (by rw [halg]; exact hmem)
  refine ⟨N, fun N' hN' ↦ ?_⟩
  rw [← pow_sub_mul_pow t hN', mul_assoc]
  exact Ideal.mul_mem_left _ _ hN

end LocalAlgebra

section ChartIdeal

open HomogeneousLocalization

variable {X : Scheme.{u}}

/-- The chart model of the ideal of sections of an ideal sheaf `J` on the blow-up over
the `a`-chart: the ideal of sections of the pullback of `J` along the chart probe,
transported to the chart ring along the global-sections isomorphism. -/
def Scheme.IdealSheafData.chartIdeal (I : X.IdealSheafData) (J : I.blowup.IdealSheafData)
    (V : X.affineOpens) {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) :
    Ideal (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) a ha)) :=
  ((J.comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso _).hom.hom

/-- Membership in the chart model of `J` is membership of the transported section in
the ideal of sections of the pullback of `J`. -/
lemma Scheme.IdealSheafData.mem_chartIdeal_iff (I : X.IdealSheafData)
    (J : I.blowup.IdealSheafData) (V : X.affineOpens) {a : Γ(X, V.1)}
    (ha : a ∈ I.ideal V)
    {z : HomogeneousLocalization.Away (reesGrading (I.ideal V)) (reesX (I.ideal V) a ha)} :
    z ∈ I.chartIdeal J V ha ↔ (Scheme.ΓSpecIso _).inv.hom z ∈
      (J.comap (I.blowupChart V ha)).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  have hx : (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
      (reesGrading (I.ideal V)) (reesX (I.ideal V) a ha)))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (reesGrading (I.ideal V)) (reesX (I.ideal V) a ha)))).inv.hom z) = z := by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
  conv_lhs => rw [← hx]
  exact CommRingCat.hom_mem_ideal_map_iso_iff _ _ _

/-- The chart model of a finite-type ideal sheaf is finitely generated. -/
lemma Scheme.IdealSheafData.chartIdeal_fg (I : X.IdealSheafData)
    {J : I.blowup.IdealSheafData} (hJ : J.FiniteType) (V : X.affineOpens)
    {a : Γ(X, V.1)} (ha : a ∈ I.ideal V) : (I.chartIdeal J V ha).FG :=
  ((hJ.comap_of_isOpenImmersion (I.blowupChart V ha)) ⟨⊤, isAffineOpen_top _⟩).map _

/-- The chart models of `J` on two charts of the same Rees algebra agree in the common
localization `B_{b·a}`: transport of the pullback of `J` along the overlap probe. The
orientation matches the hypothesis of
`AffineBlowup.exists_isLocalizationElem_pow_mul_chartFrac_mem`. -/
lemma Scheme.IdealSheafData.chartIdeal_map_awayMap (I : X.IdealSheafData)
    (J : I.blowup.IdealSheafData) (V : X.affineOpens) {a b : Γ(X, V.1)}
    (ha : a ∈ I.ideal V) (hb : b ∈ I.ideal V) :
    (I.chartIdeal J V ha).map (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
        (reesX_mem (I.ideal V) b hb)
        (mul_comm (reesX (I.ideal V) b hb) (reesX (I.ideal V) a ha))) =
      (I.chartIdeal J V hb).map (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
        (reesX_mem (I.ideal V) a ha)
        (rfl : reesX (I.ideal V) b hb * reesX (I.ideal V) a ha
          = reesX (I.ideal V) b hb * reesX (I.ideal V) a ha)) := by
  have h1 := J.map_ideal_comap_specMap_comp (I.blowupChart V ha)
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
      (reesX_mem (I.ideal V) b hb)
      (mul_comm (reesX (I.ideal V) b hb) (reesX (I.ideal V) a ha))))
  have h2 := J.map_ideal_comap_specMap_comp (I.blowupChart V hb)
    (CommRingCat.ofHom (HomogeneousLocalization.awayMap (reesGrading (I.ideal V))
      (reesX_mem (I.ideal V) a ha)
      (rfl : reesX (I.ideal V) b hb * reesX (I.ideal V) a ha
        = reesX (I.ideal V) b hb * reesX (I.ideal V) a ha)))
  -- the two overlap probes agree
  have hmid := congrArg
    (fun q : Spec (CommRingCat.of (HomogeneousLocalization.Away (reesGrading (I.ideal V))
        (reesX (I.ideal V) b hb * reesX (I.ideal V) a ha))) ⟶ I.blowup ↦
      ((J.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso _).hom.hom)
    (I.specMap_awayMap_blowupChart V hb ha)
  exact (h1.symm.trans (hmid.symm.trans h2) :)

end ChartIdeal

section MapMembership

variable {X Y : Scheme.{u}}

/-- **Membership in the pushforward ideal through a covering family of affine probes**:
let `g : Y ⟶ X` be quasi-compact, `K` an ideal sheaf on `Y`, `V` an affine open of `X`
and `x` a section over `V`. Suppose given open-immersion probes `cᵢ : Spec Sᵢ ⟶ Y`
lying over `V` and covering `g⁻¹(V)`, such that the pullback of `x` to each probe lies
in the ideal of sections of the pullback of `K`. Then `x` lies in the ideal of the
pushforward `K.map g` over `V`. This makes the blueprint's maximal candidate
`π₎(I_E^d J)` accessible chart by chart. -/
lemma Scheme.IdealSheafData.mem_ideal_map_of_probes (K : Y.IdealSheafData)
    (g : Y ⟶ X) [QuasiCompact g] (V : X.affineOpens) (x : Γ(X, V.1))
    {ι : Type u} {S : ι → CommRingCat.{u}} (c : ∀ i, Spec (S i) ⟶ Y)
    [∀ i, IsOpenImmersion (c i)]
    (hcov : (g ⁻¹ᵁ V.1 : Set Y) ⊆ ⋃ i, Set.range (c i))
    (hle : ∀ i, (⊤ : (Spec (S i)).Opens) ≤ (c i ≫ g) ⁻¹ᵁ V.1)
    (hx : ∀ i, ((c i ≫ g).appLE V.1 ⊤ (hle i)).hom x ∈
      (K.comap (c i)).ideal ⟨⊤, isAffineOpen_top _⟩) :
    x ∈ (K.map g).ideal V := by
  haveI : QuasiCompact (K.subschemeι ≫ g) := inferInstance
  change x ∈ (K.subschemeι ≫ g).ker.ideal V
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
  apply K.subscheme.IsSheaf.section_ext
  intro p hp
  -- the image of `p` in `Y` lies over `V`, hence in the range of some probe
  have hpV : K.subschemeι p ∈ (g ⁻¹ᵁ V.1 : Set Y) := by
    change g (K.subschemeι p) ∈ V.1
    rw [← Scheme.Hom.comp_apply]
    exact hp
  obtain ⟨_, ⟨i, rfl⟩, y, hy⟩ := hcov hpV
  -- the pullback of the probe to the subscheme
  haveI : IsClosedImmersion (pullback.fst (c i) K.subschemeι) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  have hprange : p ∈ Set.range (pullback.snd (c i) K.subschemeι) := by
    rw [Scheme.Pullback.range_snd]
    exact ⟨y, hy⟩
  obtain ⟨q, hq⟩ := hprange
  -- the composite of the pullback square with the probe
  have hcomp : pullback.snd (c i) K.subschemeι ≫ K.subschemeι ≫ g =
      pullback.fst (c i) K.subschemeι ≫ (c i ≫ g) := by
    rw [← Category.assoc, ← Limits.pullback.condition, Category.assoc]
  -- the witnessing open: the image of the preimage of `(subschemeι ≫ g)⁻¹(V)`
  refine ⟨pullback.snd (c i) K.subschemeι ''ᵁ
    (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1)), ?_,
    ⟨q, ?_, hq⟩, ?_⟩
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact hw
  · change pullback.snd (c i) K.subschemeι q ∈ (K.subschemeι ≫ g) ⁻¹ᵁ V.1
    rw [hq]
    exact hp
  -- both restrictions are computed by pulling back to the probe
  rw [map_zero]
  apply ((pullback.snd (c i) K.subschemeι).appIso
    (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1))
      ).commRingCatIsoToRingEquiv.injective
  rw [map_zero, ← RingEquiv.coe_toRingHom, Iso.commRingCatIsoToRingEquiv_toRingHom,
    Scheme.Hom.appIso_hom']
  simp only [homOfLE_leOfHom, Scheme.Hom.app_eq_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
  -- exchange the composite for the probe composite and split off the probe map
  rw [Scheme.Hom.appLE_eq_of_eq hcomp]
  rw [← Scheme.Hom.appLE_comp_appLE (pullback.fst (c i) K.subschemeι) (c i ≫ g)
    V.1 ⊤ (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1))
    (hle i) le_top]
  rw [CommRingCat.comp_apply]
  -- the probe image of `x` is killed by the closed immersion from the subscheme part
  have h0 : ((pullback.fst (c i) K.subschemeι).app ⊤).hom
      (((c i ≫ g).appLE V.1 ⊤ (hle i)).hom x) = 0 := by
    apply Scheme.Hom.ideal_ker_le _ ⟨⊤, isAffineOpen_top _⟩
    rw [Scheme.IdealSheafData.ker_fst_of_isClosedImmersion,
      Scheme.IdealSheafData.ker_subschemeι]
    exact hx i
  have hexp : (pullback.fst (c i) K.subschemeι).appLE ⊤
      (pullback.snd (c i) K.subschemeι ⁻¹ᵁ ((K.subschemeι ≫ g) ⁻¹ᵁ V.1)) le_top =
      (pullback.fst (c i) K.subschemeι).app ⊤ ≫
        (Limits.pullback (c i) K.subschemeι).presheaf.map (homOfLE le_top).op := rfl
  rw [hexp, CommRingCat.comp_apply, h0, map_zero]

end MapMembership

section UniformNumerator

open HomogeneousLocalization

variable {A : Type u} [CommRing A] (I₀ : Ideal A)

/-- **The uniform numerator construction** (Steps 2–3 of the blueprint proof of Stacks
Tag 0803, ring-level form): given a finite generating set `s` of `I₀`, a family of
chart ideals `Jc` agreeing on overlaps, and a chart fraction `g/aᵉ` lying in the chart
ideal of the `a`-chart, there is a threshold `d₀` such that for every `d ≥ d₀` there is
a numerator `m ∈ I₀ᵈ` with `m/aᵈ = g/aᵉ` on the `a`-chart whose fraction `m/bᵈ` lies in
the chart ideal of every `b`-chart, `b ∈ s`. -/
lemma AffineBlowup.exists_uniform_numerator
    (s : Finset A) (hs : Ideal.span (s : Set A) = I₀)
    (Jc : ∀ (b : A) (hb : b ∈ I₀), Ideal (HomogeneousLocalization.Away (reesGrading I₀)
      (reesX I₀ b hb)))
    (hJc : ∀ (a b : A) (ha : a ∈ I₀) (hb : b ∈ I₀),
      (Jc a ha).map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ b hb)
        (mul_comm (reesX I₀ b hb) (reesX I₀ a ha))) =
      (Jc b hb).map (HomogeneousLocalization.awayMap (reesGrading I₀) (reesX_mem I₀ a ha)
        (rfl : reesX I₀ b hb * reesX I₀ a ha = reesX I₀ b hb * reesX I₀ a ha)))
    {a : A} (has : a ∈ s) {e : ℕ} {g : A} (hg : g ∈ I₀ ^ e)
    (hμ : AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span has) hg ∈
      Jc a (hs ▸ Ideal.subset_span has)) :
    ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ (m : A) (hm : m ∈ I₀ ^ d),
      AffineBlowup.awayAlgebraMap I₀ (reesX I₀ a (hs ▸ Ideal.subset_span has)) m =
        AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span has) hg *
          AffineBlowup.awayAlgebraMap I₀ (reesX I₀ a (hs ▸ Ideal.subset_span has)) a ^ d ∧
      ∀ (b : A) (hbs : b ∈ s), AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span hbs) hm ∈
        Jc b (hs ▸ Ideal.subset_span hbs) := by
  classical
  have ha' : a ∈ I₀ := hs ▸ Ideal.subset_span has
  -- clearing exponents for each chart in the generating set
  have hclear : ∀ (b : A) (hbs : b ∈ s), ∃ N : ℕ, ∀ N' ≥ N,
      HomogeneousLocalization.Away.isLocalizationElem
          (reesX_mem I₀ b (hs ▸ Ideal.subset_span hbs)) (reesX_mem I₀ a ha') ^ N' *
        AffineBlowup.chartFrac I₀ (hs ▸ Ideal.subset_span hbs) hg ∈
      Jc b (hs ▸ Ideal.subset_span hbs) := fun b hbs ↦
    AffineBlowup.exists_isLocalizationElem_pow_mul_chartFrac_mem I₀ ha'
      (hs ▸ Ideal.subset_span hbs) (Jc a ha') (Jc b (hs ▸ Ideal.subset_span hbs))
      (hJc a b ha' (hs ▸ Ideal.subset_span hbs)) hg hμ
  choose N hN using hclear
  refine ⟨(s.attach.sup fun b ↦ N b.1 b.2) + e, fun d hd ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, d = k + e := ⟨d - e, by omega⟩
  have hkN : ∀ (b : A) (hbs : b ∈ s), N b hbs ≤ k := by
    intro b hbs
    have h1 : N b hbs ≤ s.attach.sup fun b ↦ N b.1 b.2 :=
      Finset.le_sup (f := fun b : { x // x ∈ s } ↦ N b.1 b.2)
        (Finset.mem_attach _ ⟨b, hbs⟩)
    omega
  have hm : a ^ k * g ∈ I₀ ^ (k + e) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow ha' k) hg
  refine ⟨a ^ k * g, hm, ?_, ?_⟩
  · rw [← AffineBlowup.chartFrac_mul_awayAlgebraMap_pow I₀ ha' hm,
      AffineBlowup.chartFrac_self_pow_mul I₀ ha' hg hm]
  · intro b hbs
    rw [AffineBlowup.chartFrac_pow_mul I₀ ha' (hs ▸ Ideal.subset_span hbs) hg hm]
    exact hN b hbs k (hkN b hbs)

end UniformNumerator

section ChartMembership

open HomogeneousLocalization

variable {X : Scheme.{u}}

/-- The image of a factored element under a ring homomorphism, commuted into the shape
of a power times a factor. Keeping the rings abstract makes this cheap to instantiate
at the section rings of blow-up charts. -/
private lemma ringHom_pow_mul_eq {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) {x y z : R} (d : ℕ) (h : y * x ^ d = z) :
    (f x) ^ d * f y = f z := by
  rw [← h, map_mul, map_pow, mul_comm]

/-- **Membership criterion for the pullback of `I_Eᵈ · J'` along an open-immersion
probe**, generic in the probe ring: an element factoring as `yPᵈ · yQ` with `yP` in the
pulled-back exceptional ideal and `yQ` in the pulled-back `J'` lies in the pullback of
the product. -/
lemma Scheme.IdealSheafData.mem_ideal_comap_pow_mul_probe
    (I : X.IdealSheafData) (J' : I.blowup.IdealSheafData) (d : ℕ)
    {S : CommRingCat.{u}} (c : Spec S ⟶ I.blowup) [IsOpenImmersion c]
    {x yP yQ : Γ(Spec S, ⊤)}
    (hP : yP ∈ ((I.comap I.blowupMap).comap c).ideal ⟨⊤, isAffineOpen_top _⟩)
    (hQ : yQ ∈ (J'.comap c).ideal ⟨⊤, isAffineOpen_top _⟩)
    (hx : yP ^ d * yQ = x) :
    x ∈ ((((I.comap I.blowupMap) ^ d) * J').comap c).ideal ⟨⊤, isAffineOpen_top _⟩ := by
  rw [Scheme.IdealSheafData.ideal_comap_pow_mul_comap_probe I J' d c, ← hx]
  exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hP d) hQ

/-- If the chart fraction `m/bᵈ` of a section `m ∈ I(V)ᵈ` lies in the chart model of
`J`, then the chart image of `m` lies in the ideal of sections of the pullback of
`I_Eᵈ · J` on the `b`-chart. This is the membership input both for the pushforward
candidate and for the final generation argument. -/
lemma Scheme.IdealSheafData.blowupChartSection_mem_of_chartFrac_mem
    (I : X.IdealSheafData) (J : I.blowup.IdealSheafData) (V : X.affineOpens)
    {b : Γ(X, V.1)} (hb : b ∈ I.ideal V) {d : ℕ}
    {m : Γ(X, V.1)} (hm : m ∈ (I.ideal V) ^ d)
    (hfrac : AffineBlowup.chartFrac (I.ideal V) hb hm ∈ I.chartIdeal J V hb) :
    (I.blowupChartSection V hb).hom m ∈
      ((((I.comap I.blowupMap) ^ d) * J).comap (I.blowupChart V hb)).ideal
        ⟨⊤, isAffineOpen_top _⟩ :=
  Scheme.IdealSheafData.mem_ideal_comap_pow_mul_probe I J d (I.blowupChart V hb)
    ((I.ideal_comap_comap_blowupChart_self V hb).ge (Ideal.subset_span rfl))
    ((I.mem_chartIdeal_iff J V hb).mp hfrac)
    (ringHom_pow_mul_eq
      (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
        (reesGrading (I.ideal V)) (reesX (I.ideal V) b hb)))).inv.hom d
      (AffineBlowup.chartFrac_mul_awayAlgebraMap_pow (I.ideal V) hb hm))

end ChartMembership

section Generation

open HomogeneousLocalization

variable {X : Scheme.{u}}

/-- Transport of a generating set along an isomorphism of `CommRingCat`. -/
private lemma span_eq_of_map_iso_span {R S : CommRingCat.{u}} (E : R ≅ S)
    {P : Ideal R} {G : Set S} (h : Ideal.span G = P.map E.hom.hom) :
    P = Ideal.span (E.inv.hom '' G) := by
  have h1 := congrArg (Ideal.map E.inv.hom) h
  rw [Ideal.map_span, Ideal.map_map, ← CommRingCat.hom_comp, E.hom_inv_id,
    CommRingCat.hom_id, Ideal.map_id] at h1
  exact h1.symm

/-- **The generation step of Stacks Tag 0803**, ring-level form: if every generator
`μ` of an ideal spanned by `f '' G` satisfies `μ · ψ(β)ᵈ = ψ(m)` for some `m` in an
ideal `LI` of the base ring, then `(f (ψ β))ᵈ · span (f '' G)` is contained in the
extension of `LI` along `f ∘ ψ`. -/
private lemma span_pow_mul_span_le_map {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (ψ : A →+* B) (f : B →+* C) (g : A →+* C) (hgf : ∀ a, f (ψ a) = g a)
    (β : A) (d : ℕ) (G : Set B) {LI : Ideal A}
    (hgen : ∀ μ ∈ G, ∃ m ∈ LI, μ * ψ β ^ d = ψ m) :
    Ideal.span {g β} ^ d * Ideal.span (f '' G) ≤ LI.map g := by
  rw [Ideal.span_singleton_pow, Ideal.mul_le]
  rintro r hr z hz
  rw [Ideal.mem_span_singleton] at hr
  obtain ⟨cc, rfl⟩ := hr
  induction hz using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨μ0, hμ0, rfl⟩ := hw
    obtain ⟨m', hmLI, hfm⟩ := hgen μ0 hμ0
    have hkey : g β ^ d * cc * f μ0 = cc * g m' := by
      rw [← hgf m', ← hgf β, ← hfm, map_mul, map_pow]
      ring
    rw [hkey]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hmLI)
  | zero =>
    rw [mul_zero]
    exact zero_mem _
  | add u v hu hv ihu ihv =>
    rw [mul_add]
    exact add_mem ihu ihv
  | smul a u hu ihu =>
    rw [smul_eq_mul, show g β ^ d * cc * (a * u) =
      a * (g β ^ d * cc * u) from by ring]
    exact Ideal.mul_mem_left _ _ ihu

set_option maxHeartbeats 1600000 in
/-- **The chartwise generation inequality** (Step 4 of the blueprint proof of Stacks
Tag 0803): if every generator of the chart model of `J` on the `b`-chart has a
numerator in `L(V)`, then the ideal of `I_Eᵈ · J` on the chart is contained in that of
the inverse image of `L`. -/
lemma Scheme.IdealSheafData.ideal_pow_mul_le_comap_of_numerators
    (I : X.IdealSheafData) (J : I.blowup.IdealSheafData) (L : X.IdealSheafData)
    (V : X.affineOpens) {b : Γ(X, V.1)} (hb : b ∈ I.ideal V) (d : ℕ)
    (G : Finset (HomogeneousLocalization.Away (reesGrading (I.ideal V))
      (reesX (I.ideal V) b hb)))
    (hG : Ideal.span (G : Set _) = I.chartIdeal J V hb)
    (hgen : ∀ μ ∈ G, ∃ m' ∈ L.ideal V,
      μ * AffineBlowup.awayAlgebraMap (I.ideal V) (reesX (I.ideal V) b hb) b ^ d =
        AffineBlowup.awayAlgebraMap (I.ideal V) (reesX (I.ideal V) b hb) m') :
    (((I.comap I.blowupMap) ^ d) * J).ideal
        ⟨I.blowupChart V hb ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩ ≤
      (L.comap I.blowupMap).ideal
        ⟨I.blowupChart V hb ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩ := by
  apply Scheme.IdealSheafData.ideal_le_of_comap_probe (I.blowupChart V hb)
  refine le_of_eq_of_le
    (Scheme.IdealSheafData.ideal_comap_pow_mul_comap_blowupChart I J d V hb) ?_
  refine le_of_le_of_eq ?_ (Scheme.IdealSheafData.ideal_comap_comap_blowupChart I L V hb).symm
  refine le_of_eq_of_le (congrArg
    (fun Q ↦ Ideal.span {(I.blowupChartSection V hb).hom b} ^ d * Q)
    (span_eq_of_map_iso_span (Scheme.ΓSpecIso (CommRingCat.of
      (HomogeneousLocalization.Away (reesGrading (I.ideal V))
        (reesX (I.ideal V) b hb)))) hG)) ?_
  exact span_pow_mul_span_le_map
    (AffineBlowup.awayAlgebraMap (I.ideal V) (reesX (I.ideal V) b hb))
    (Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away
      (reesGrading (I.ideal V)) (reesX (I.ideal V) b hb)))).inv.hom
    (I.blowupChartSection V hb).hom (fun _ ↦ rfl)
    b d (G : Set _) hgen

end Generation

section Main

variable {X : Scheme.{u}}

/-- Pullback of a finite supremum of ideal sheaves. -/
private lemma comap_finset_sup {Y : Scheme.{u}} {α : Type*} (T : Finset α)
    (F : α → X.IdealSheafData) (f : Y ⟶ X) :
    (T.sup F).comap f = T.sup fun a ↦ (F a).comap f := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using (Scheme.IdealSheafData.map_gc f).l_bot
  | insert a T' ha ih =>
    rw [Finset.sup_insert, Finset.sup_insert, Scheme.IdealSheafData.comap_sup, ih]

/-- The bottom ideal sheaf is of finite type. -/
private lemma finiteType_bot : (⊥ : X.IdealSheafData).FiniteType := fun U ↦ by
  have h : (⊥ : X.IdealSheafData).ideal U = ⊥ :=
    congrFun Scheme.IdealSheafData.ideal_bot U
  rw [h]
  exact Submodule.fg_bot

set_option maxHeartbeats 3200000 in
/-- **Finite-degree approximation on the blow-up itself** (Stacks Project Tag 0803):
for finite-type centers `I` on a qcqs scheme `X` and `J` on the blow-up of `I`, there
are `d ≥ 1` and a finite-type `L ≤ I^d` whose inverse image ideal on the blow-up is
`I_E^d · J`. -/
theorem Scheme.IdealSheafData.exists_finiteDegree_center_le_blowup'
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (hI : I.FiniteType) (J : I.blowup.IdealSheafData)
    (hJ : J.FiniteType) :
    ∃ (d : ℕ) (L : X.IdealSheafData), 0 < d ∧ L.FiniteType ∧ L ≤ I ^ d ∧
      L.comap I.blowupMap = (I.comap I.blowupMap) ^ d * J := by
  classical
  haveI : QuasiCompact I.blowupMap := Scheme.IdealSheafData.quasiCompact_blowupMap hI
  -- a finite affine cover of `X`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : X.affineOpens ↦ (V.1 : Set X)) (fun V ↦ V.1.isOpen) (by
      intro x _
      have hx : x ∈ (⊤ : X.Opens) := trivial
      rw [← iSup_affineOpens_eq_top X] at hx
      obtain ⟨V, hV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact Set.mem_iUnion.mpr ⟨V, hV⟩)
  -- generators of the center over each affine open
  choose s hs using fun V : X.affineOpens ↦ hI V
  -- generators of the chart models of `J`
  choose G hG using fun (V : X.affineOpens) (b : Γ(X, V.1)) (hb : b ∈ I.ideal V) ↦
    I.chartIdeal_fg hJ V hb
  -- numerator thresholds for every chart generator
  have hnum : ∀ (V : X.affineOpens) (b : Γ(X, V.1)) (hbs : b ∈ s V)
      (μ : HomogeneousLocalization.Away (reesGrading (I.ideal V))
        (reesX (I.ideal V) b ((hs V) ▸ Ideal.subset_span hbs)))
      (_ : μ ∈ G V b ((hs V) ▸ Ideal.subset_span hbs)),
      ∃ d₀ : ℕ, ∀ d ≥ d₀, ∃ (m : Γ(X, V.1)) (hm : m ∈ (I.ideal V) ^ d),
        AffineBlowup.awayAlgebraMap (I.ideal V)
            (reesX (I.ideal V) b ((hs V) ▸ Ideal.subset_span hbs)) m =
          μ * AffineBlowup.awayAlgebraMap (I.ideal V)
            (reesX (I.ideal V) b ((hs V) ▸ Ideal.subset_span hbs)) b ^ d ∧
        ∀ (b' : Γ(X, V.1)) (hbs' : b' ∈ s V),
          AffineBlowup.chartFrac (I.ideal V) ((hs V) ▸ Ideal.subset_span hbs') hm ∈
            I.chartIdeal J V ((hs V) ▸ Ideal.subset_span hbs') := by
    intro V b hbs μ hμG
    obtain ⟨e, g, hg, rfl⟩ := AffineBlowup.chartFrac_surjective (I.ideal V)
      ((hs V) ▸ Ideal.subset_span hbs) μ
    exact AffineBlowup.exists_uniform_numerator (I.ideal V) (s V) (hs V)
      (fun b' hb' ↦ I.chartIdeal J V hb')
      (fun a' b' ha' hb' ↦ I.chartIdeal_map_awayMap J V ha' hb') hbs hg
      ((hG V b ((hs V) ▸ Ideal.subset_span hbs)) ▸ Ideal.subset_span hμG)
  choose d₀f hd₀f using hnum
  -- one global degree dominating all thresholds
  refine ⟨1 + t.sup (fun V ↦ (s V).attach.sup fun b ↦
    (G V b.1 ((hs V) ▸ Ideal.subset_span b.2)).attach.sup fun μ ↦
      d₀f V b.1 b.2 μ.1 μ.2), ?_⟩
  set D : ℕ := 1 + t.sup (fun V ↦ (s V).attach.sup fun b ↦
    (G V b.1 ((hs V) ▸ Ideal.subset_span b.2)).attach.sup fun μ ↦
      d₀f V b.1 b.2 μ.1 μ.2) with hD
  have hDge : ∀ (V : X.affineOpens), V ∈ t → ∀ (b : Γ(X, V.1)) (hbs : b ∈ s V)
      (μ : _) (hμG : μ ∈ G V b ((hs V) ▸ Ideal.subset_span hbs)),
      d₀f V b hbs μ hμG ≤ D := by
    intro V hVt b hbs μ hμG
    have h1 : d₀f V b hbs μ hμG ≤
        (G V b ((hs V) ▸ Ideal.subset_span hbs)).attach.sup fun μ' ↦
          d₀f V b hbs μ'.1 μ'.2 :=
      Finset.le_sup (f := fun μ' ↦ d₀f V b hbs μ'.1 μ'.2) (Finset.mem_attach _ ⟨μ, hμG⟩)
    have h2 : ((G V b ((hs V) ▸ Ideal.subset_span hbs)).attach.sup fun μ' ↦
        d₀f V b hbs μ'.1 μ'.2) ≤
        (s V).attach.sup fun b' ↦ (G V b'.1 ((hs V) ▸ Ideal.subset_span b'.2)).attach.sup
          fun μ' ↦ d₀f V b'.1 b'.2 μ'.1 μ'.2 :=
      Finset.le_sup (f := fun b' : { x // x ∈ s V } ↦
        (G V b'.1 ((hs V) ▸ Ideal.subset_span b'.2)).attach.sup fun μ' ↦
          d₀f V b'.1 b'.2 μ'.1 μ'.2) (Finset.mem_attach _ ⟨b, hbs⟩)
    have h3 : ((s V).attach.sup fun b' ↦
        (G V b'.1 ((hs V) ▸ Ideal.subset_span b'.2)).attach.sup
          fun μ' ↦ d₀f V b'.1 b'.2 μ'.1 μ'.2) ≤
        t.sup (fun V' ↦ (s V').attach.sup fun b' ↦
          (G V' b'.1 ((hs V') ▸ Ideal.subset_span b'.2)).attach.sup fun μ' ↦
            d₀f V' b'.1 b'.2 μ'.1 μ'.2) :=
      Finset.le_sup hVt
    omega
  -- the numerators at the global degree
  have hmex : ∀ (V : X.affineOpens), V ∈ t → ∀ (b : Γ(X, V.1)) (hbs : b ∈ s V)
      (μ : _) (hμG : μ ∈ G V b ((hs V) ▸ Ideal.subset_span hbs)),
      ∃ (m : Γ(X, V.1)) (hm : m ∈ (I.ideal V) ^ D),
        AffineBlowup.awayAlgebraMap (I.ideal V)
            (reesX (I.ideal V) b ((hs V) ▸ Ideal.subset_span hbs)) m =
          μ * AffineBlowup.awayAlgebraMap (I.ideal V)
            (reesX (I.ideal V) b ((hs V) ▸ Ideal.subset_span hbs)) b ^ D ∧
        ∀ (b' : Γ(X, V.1)) (hbs' : b' ∈ s V),
          AffineBlowup.chartFrac (I.ideal V) ((hs V) ▸ Ideal.subset_span hbs') hm ∈
            I.chartIdeal J V ((hs V) ▸ Ideal.subset_span hbs') :=
    fun V hVt b hbs μ hμG ↦ hd₀f V b hbs μ hμG D (hDge V hVt b hbs μ hμG)
  choose m hmI hmψ hmJ using hmex
  -- membership of the numerators in the maximal candidate
  have hmC : ∀ (V : X.affineOpens) (hVt : V ∈ t) (b : Γ(X, V.1)) (hbs : b ∈ s V)
      (μ : _) (hμG : μ ∈ G V b ((hs V) ▸ Ideal.subset_span hbs)),
      m V hVt b hbs μ hμG ∈
        (I ^ D ⊓ (((I.comap I.blowupMap) ^ D * J).map I.blowupMap)).ideal V := by
    intro V hVt b hbs μ hμG
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · have heq : (I ^ D).ideal V = (I.ideal V) ^ D := by
        rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
      exact heq.ge (hmI V hVt b hbs μ hμG)
    · refine Scheme.IdealSheafData.mem_ideal_map_of_probes _ I.blowupMap V _
        (c := fun b' : ↥(s V) ↦
          I.blowupChart V ((hs V) ▸ Ideal.subset_span b'.2))
        (I.preimage_subset_iUnion_range_blowupChart V (hs V))
        (fun b' ↦ I.blowupChart_comp_blowupMap_preimage V
          ((hs V) ▸ Ideal.subset_span b'.2)) ?_
      intro b'
      have happ := I.appLE_blowupChart_comp_blowupMap V
        ((hs V) ▸ Ideal.subset_span b'.2)
        (I.blowupChart_comp_blowupMap_preimage V ((hs V) ▸ Ideal.subset_span b'.2))
      have hmem := I.blowupChartSection_mem_of_chartFrac_mem J V
        ((hs V) ▸ Ideal.subset_span b'.2) (hmI V hVt b hbs μ hμG)
        (hmJ V hVt b hbs μ hμG b'.1 b'.2)
      exact (congrArg (fun F ↦ CommRingCat.Hom.hom F (m V hVt b hbs μ hμG))
        happ).symm ▸ hmem
  -- extraction of a finite-type subsheaf through the numerators, per cover member
  have hLV : ∀ (V : X.affineOpens), V ∈ t → ∃ LV : X.IdealSheafData,
      LV ≤ I ^ D ⊓ (((I.comap I.blowupMap) ^ D * J).map I.blowupMap) ∧
      LV.FiniteType ∧ ∀ (hVt : V ∈ t), LV.ideal V = Ideal.span
        (((s V).attach.biUnion fun b ↦
          (G V b.1 ((hs V) ▸ Ideal.subset_span b.2)).attach.image fun μ ↦
            m V hVt b.1 b.2 μ.1 μ.2 : Finset Γ(X, V.1)) : Set Γ(X, V.1)) := by
    intro V hVt
    obtain ⟨LV, h1, h2, h3⟩ := Scheme.IdealSheafData.exists_finiteType_le_ideal_eq
      (I ^ D ⊓ (((I.comap I.blowupMap) ^ D * J).map I.blowupMap)) V
      (F := Ideal.span (((s V).attach.biUnion fun b ↦
        (G V b.1 ((hs V) ▸ Ideal.subset_span b.2)).attach.image fun μ ↦
          m V hVt b.1 b.2 μ.1 μ.2 : Finset Γ(X, V.1)) : Set Γ(X, V.1)))
      ⟨_, rfl⟩ (by
        rw [Ideal.span_le]
        intro x hx
        rw [Finset.mem_coe, Finset.mem_biUnion] at hx
        obtain ⟨b, -, hximg⟩ := hx
        rw [Finset.mem_image] at hximg
        obtain ⟨μ, -, rfl⟩ := hximg
        exact hmC V hVt b.1 b.2 μ.1 μ.2)
    exact ⟨LV, h1, h2, fun _ ↦ h3⟩
  choose LV hLVle hLVft hLVid using hLV
  refine ⟨t.attach.sup fun V ↦ LV V.1 V.2,
    Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 _), ?_, ?_, ?_⟩
  · -- finite type: finite supremum of finite-type subsheaves
    exact Finset.sup_induction finiteType_bot
      (fun _ ha _ hb ↦ Scheme.IdealSheafData.FiniteType.sup ha hb)
      fun V _ ↦ hLVft V.1 V.2
  · -- contained in `I ^ D`
    exact Finset.sup_le fun V _ ↦ (hLVle V.1 V.2).trans inf_le_left
  · -- the inverse image ideal is `I_E^D · J`
    apply le_antisymm
    · -- `≤`: from the pushforward bound, by the Galois connection
      rw [comap_finset_sup]
      refine Finset.sup_le fun V _ ↦ ?_
      have h1 : LV V.1 V.2 ≤ ((I.comap I.blowupMap) ^ D * J).map I.blowupMap :=
        (hLVle V.1 V.2).trans inf_le_right
      exact ((Scheme.IdealSheafData.comap_mono I.blowupMap) h1).trans
        (Scheme.IdealSheafData.comap_map_le _ _)
    · -- `≥`: chartwise generation by the numerators
      refine Scheme.IdealSheafData.le_of_iSup_eq_top
        (fun p : Σ V : { V // V ∈ t }, { b // b ∈ s V.1 } ↦
          ⟨I.blowupChart p.1.1 ((hs p.1.1) ▸ Ideal.subset_span p.2.2) ''ᵁ ⊤,
            (isAffineOpen_top _).image_of_isOpenImmersion _⟩) ?_ ?_
      · -- the chart images cover the blow-up
        rw [eq_top_iff]
        intro x _
        obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (I.blowupMap x)))
        have hx2 : x ∈ (I.blowupMap ⁻¹ᵁ V.1 : Set I.blowup) := hxV
        have hx3 := I.preimage_subset_iUnion_range_blowupChart V (hs V) hx2
        obtain ⟨b', hxr⟩ := Set.mem_iUnion.mp hx3
        obtain ⟨z, hz⟩ := hxr
        exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hVt⟩, b'⟩, ⟨z, trivial, hz⟩⟩
      · -- the generation inequality on each chart
        rintro ⟨⟨V, hVt⟩, b'⟩
        refine Scheme.IdealSheafData.ideal_pow_mul_le_comap_of_numerators I J _ V
          ((hs V) ▸ Ideal.subset_span b'.2) D
          (G V b'.1 ((hs V) ▸ Ideal.subset_span b'.2))
          (hG V b'.1 ((hs V) ▸ Ideal.subset_span b'.2)) ?_
        intro μ0 hμ0
        refine ⟨m V hVt b'.1 b'.2 μ0 hμ0, ?_, (hmψ V hVt b'.1 b'.2 μ0 hμ0).symm⟩
        have h1 : m V hVt b'.1 b'.2 μ0 hμ0 ∈ (LV V hVt).ideal V := by
          rw [hLVid V hVt hVt]
          refine Ideal.subset_span ?_
          rw [Finset.mem_coe, Finset.mem_biUnion]
          exact ⟨⟨b'.1, b'.2⟩, Finset.mem_attach _ _, Finset.mem_image.mpr
            ⟨⟨μ0, hμ0⟩, Finset.mem_attach _ _, rfl⟩⟩
        have h2 : LV V hVt ≤ t.attach.sup fun V' ↦ LV V'.1 V'.2 :=
          Finset.le_sup (f := fun V' : { x // x ∈ t } ↦ LV V'.1 V'.2)
            (Finset.mem_attach _ ⟨V, hVt⟩)
        exact h2 V h1

end Main

end AlgebraicGeometry
