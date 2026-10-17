/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.NoetherianApproximation.GluingStages
public import WeilConjectures.AlgebraicGeometry.OpensGlueData

/-!
# Chart maps of subrings of section rings

Let `U` be an open of a scheme `S` and `A ⊆ Γ(S, U)` a subring. For every open `W ≤ U` the
inclusion `A ⊆ Γ(S, U) ⟶ Γ(S, W)` induces a morphism `W ⟶ Spec A`
(`AlgebraicGeometry.Scheme.subringChart`). These are the chart maps from `S` to the charts of
the finite-type stages of a finite affine gluing presentation.

If `U` is affine, the chart maps are *epimorphic towards affine schemes* on the opens
`⋃ᵢ D(kᵢ)` of `Spec A` (`AlgebraicGeometry.Scheme.chartLift_cancel`): two morphisms out of
`⋃ᵢ D(kᵢ) ⊆ Spec A` into an affine scheme agree as soon as they agree on `⋃ᵢ D_S(kᵢ) ⊆ S`.
This is the geometric form of the fact that `A[1/k] → Γ(S, D(k)) = Γ(S, U)[1/k]` is injective
(localization is exact). Moreover a morphism `⋃ᵢ D_S(kᵢ) ⟶ Spec R` extends to `⋃ᵢ D(kᵢ)` as soon
as on every `D_S(kᵢ)` it is given by sections lying in `A[1/kᵢ]`
(`AlgebraicGeometry.Scheme.exists_chartLift_comp_eq`), and we have a criterion for the image of
such an extension (`AlgebraicGeometry.Scheme.range_subset_iSup_basicOpen`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {S : Scheme.{u}}

lemma resLE_comp {U W W' : S.Opens} (h : W ≤ U) (h' : W' ≤ W) :
    S.resLE h ≫ S.resLE h' = S.resLE (h'.trans h) := by
  rw [resLE, resLE, ← Functor.map_comp]
  rfl

lemma resLE_resLE_apply {U W W' : S.Opens} (h : W ≤ U) (h' : W' ≤ W) (x : Γ(S, U)) :
    S.resLE h' (S.resLE h x) = S.resLE (h'.trans h) x := by
  rw [← resLE_comp h h']
  rfl

@[reassoc]
lemma homOfLE_toSpecΓ_SpecMap {W W' : S.Opens} (h : W' ≤ W) {R : CommRingCat.{u}}
    (ρ : R ⟶ Γ(S, W)) :
    S.homOfLE h ≫ W.toSpecΓ ≫ Spec.map ρ = W'.toSpecΓ ≫ Spec.map (ρ ≫ S.resLE h) := by
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp]

/-- On an affine open `W`, morphisms `W ⟶ Spec R` induced by ring maps `R ⟶ Γ(S, W)` determine
the ring maps. -/
lemma toSpecΓ_SpecMap_injective {W : S.Opens} (hW : IsAffineOpen W) {R : CommRingCat.{u}}
    {φ ψ : R ⟶ Γ(S, W)} (h : W.toSpecΓ ≫ Spec.map φ = W.toSpecΓ ≫ Spec.map ψ) : φ = ψ := by
  rw [← hW.isoSpec_hom, cancel_epi] at h
  exact Spec.map_injective h

/-- If `W' ≤ W ≤ D(s)`, restriction maps the localization subring `A[1/s]|_W` into
`A[1/s]|_{W'}`. -/
lemma resLE_mem_localizationSubring_of_mem {U : S.Opens} {A : Subring Γ(S, U)} {s : Γ(S, U)}
    {W W' : S.Opens} (hW : W ≤ S.basicOpen s) (h' : W' ≤ W) {z : Γ(S, W)}
    (hz : z ∈ localizationSubring A s W hW) :
    S.resLE h' z ∈ localizationSubring A s W' (h'.trans hW) := by
  have hinv : S.resLE h' (basicOpenInv s W hW) = basicOpenInv s W' (h'.trans hW) := by
    have h1 := resLE_mul_basicOpenInv s W hW
    have h2 := resLE_mul_basicOpenInv s W' (h'.trans hW)
    have h3 : S.resLE ((h'.trans hW).trans (S.basicOpen_le s)) s *
        S.resLE h' (basicOpenInv s W hW) = 1 := by
      rw [← resLE_resLE_apply (hW.trans (S.basicOpen_le s)) h', ← map_mul, h1, map_one]
    calc S.resLE h' (basicOpenInv s W hW)
        = S.resLE h' (basicOpenInv s W hW) * (S.resLE ((h'.trans hW).trans (S.basicOpen_le s)) s *
            basicOpenInv s W' (h'.trans hW)) := by rw [h2, mul_one]
      _ = basicOpenInv s W' (h'.trans hW) := by rw [← mul_assoc, mul_comm _ (S.resLE _ s), h3,
            one_mul]
  rw [localizationSubring_eq_closure] at hz
  have := Subring.mem_map_of_mem (S.resLE h').hom hz
  rw [← RingHom.map_closure, Set.image_insert_eq, ← Set.image_comp] at this
  refine Subring.closure_le.mpr ?_ this
  rintro _ (rfl | ⟨y, hy, rfl⟩)
  · rw [hinv]
    exact basicOpenInv_mem_localizationSubring A s W' _
  · simp only [Function.comp_apply]
    rw [resLE_resLE_apply]
    exact resLE_mem_localizationSubring s W' _ hy

variable {U : S.Opens}

/-- The ring map `A ⟶ Γ(S, W)` induced by a subring `A ⊆ Γ(S, U)`, for `W ≤ U`. -/
noncomputable def subringRes (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U) :
    CommRingCat.of A ⟶ Γ(S, W) :=
  CommRingCat.ofHom ((S.resLE h).hom.comp A.subtype)

lemma subringRes_apply (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U) (x : A) :
    subringRes A h x = S.resLE h (x : Γ(S, U)) :=
  rfl

@[reassoc (attr := simp)]
lemma subringRes_comp_resLE (A : Subring Γ(S, U)) {W W' : S.Opens} (h : W ≤ U) (h' : W' ≤ W) :
    subringRes A h ≫ S.resLE h' = subringRes A (h'.trans h) := by
  ext x
  exact resLE_resLE_apply h h' (x : Γ(S, U))

/-- The chart map `W ⟶ Spec A` induced by a subring `A ⊆ Γ(S, U)`, for `W ≤ U`. -/
noncomputable def subringChart (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U) :
    W.toScheme ⟶ Spec (CommRingCat.of A) :=
  W.toSpecΓ ≫ Spec.map (subringRes A h)

@[reassoc (attr := simp)]
lemma homOfLE_subringChart (A : Subring Γ(S, U)) {W W' : S.Opens} (h : W ≤ U) (h' : W' ≤ W) :
    S.homOfLE h' ≫ subringChart A h = subringChart A (h'.trans h) := by
  rw [subringChart, homOfLE_toSpecΓ_SpecMap, subringRes_comp_resLE]
  rfl

/-- The chart maps are compatible with inclusions of subrings. -/
@[reassoc (attr := simp)]
lemma subringChart_comp_SpecMap_inclusion {A A' : Subring Γ(S, U)} (hAA' : A ≤ A')
    {W : S.Opens} (h : W ≤ U) :
    subringChart A' h ≫ Spec.map (CommRingCat.ofHom (Subring.inclusion hAA')) =
      subringChart A h := by
  rw [subringChart, subringChart, Category.assoc, ← Spec.map_comp]
  rfl

lemma subringChart_preimage_basicOpen (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U) (x : A) :
    subringChart A h ⁻¹ᵁ PrimeSpectrum.basicOpen x = W.ι ⁻¹ᵁ S.basicOpen (x : Γ(S, U)) := by
  rw [subringChart, Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen,
    Scheme.Opens.toSpecΓ_preimage_basicOpen, subringRes_apply, Scheme.basicOpen_res,
    Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, top_inf_eq]

lemma subringChart_preimage_iSup_basicOpen (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U)
    {σ : Type*} (k : σ → A) :
    subringChart A h ⁻¹ᵁ (⨆ i, PrimeSpectrum.basicOpen (k i)) =
      W.ι ⁻¹ᵁ ⨆ i, S.basicOpen (k i : Γ(S, U)) := by
  rw [Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_iSup]
  simp_rw [subringChart_preimage_basicOpen]

lemma range_subringChart_subset (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U)
    {σ : Type*} (k : σ → A) (hW : W ≤ ⨆ i, S.basicOpen (k i : Γ(S, U))) :
    Set.range (subringChart A h) ⊆ ((⨆ i, PrimeSpectrum.basicOpen (k i) :
      (Spec (CommRingCat.of A)).Opens) : Set (Spec (CommRingCat.of A))) := by
  rintro _ ⟨p, rfl⟩
  have hp : p ∈ subringChart A h ⁻¹ᵁ (⨆ i, PrimeSpectrum.basicOpen (k i)) := by
    rw [subringChart_preimage_iSup_basicOpen]
    exact hW p.2
  exact hp

lemma range_subringChart_subset_basicOpen (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U)
    (x : A) (hW : W ≤ S.basicOpen (x : Γ(S, U))) :
    Set.range (subringChart A h) ⊆ ((PrimeSpectrum.basicOpen x :
      (Spec (CommRingCat.of A)).Opens) : Set (Spec (CommRingCat.of A))) := by
  rintro _ ⟨p, rfl⟩
  have hp : p ∈ subringChart A h ⁻¹ᵁ PrimeSpectrum.basicOpen x := by
    rw [subringChart_preimage_basicOpen]
    exact hW p.2
  exact hp

/-- The chart map `W ⟶ Spec A`, lifted to an open `V ⊆ Spec A` containing its image. -/
noncomputable def chartLift (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U)
    (V : (Spec (CommRingCat.of A)).Opens) (hV : Set.range (subringChart A h) ⊆ V) :
    W.toScheme ⟶ V.toScheme :=
  IsOpenImmersion.lift V.ι (subringChart A h) (by rwa [Scheme.Opens.range_ι])

@[reassoc (attr := simp)]
lemma chartLift_ι (A : Subring Γ(S, U)) {W : S.Opens} (h : W ≤ U)
    (V : (Spec (CommRingCat.of A)).Opens) (hV : Set.range (subringChart A h) ⊆ V) :
    chartLift A h V hV ≫ V.ι = subringChart A h :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc]
lemma homOfLE_chartLift (A : Subring Γ(S, U)) {W W' : S.Opens} (h : W ≤ U) (h' : W' ≤ W)
    {V V' : (Spec (CommRingCat.of A)).Opens} (hVV' : V' ≤ V)
    (hV : Set.range (subringChart A h) ⊆ V) (hV' : Set.range (subringChart A (h'.trans h)) ⊆ V') :
    S.homOfLE h' ≫ chartLift A h V hV =
      chartLift A (h'.trans h) V' hV' ≫ (Spec (CommRingCat.of A)).homOfLE hVV' := by
  rw [← cancel_mono V.ι]
  simp

/-! ### Basic opens -/

section BasicOpen

variable (A : Subring Γ(S, U)) (x : A)

/-- The ring map `A[1/x] ⟶ Γ(S, D(x))`. -/
noncomputable def awayLift : Localization.Away x →+* Γ(S, S.basicOpen (x : Γ(S, U))) :=
  IsLocalization.Away.lift x (g := (subringRes A (S.basicOpen_le (x : Γ(S, U)))).hom)
    (RingedSpace.isUnit_res_basicOpen S.toRingedSpace _)

lemma awayLift_algebraMap (y : A) :
    awayLift A x (algebraMap A _ y) = S.resLE (S.basicOpen_le (x : Γ(S, U))) (y : Γ(S, U)) :=
  IsLocalization.Away.lift_eq _ _ _

lemma ofHom_algebraMap_comp_awayLift :
    CommRingCat.ofHom (algebraMap (CommRingCat.of A) (Localization.Away x)) ≫
      CommRingCat.ofHom (awayLift A x) = subringRes A (S.basicOpen_le (x : Γ(S, U))) := by
  ext y
  exact awayLift_algebraMap A x y

/-- `A[1/x] ⟶ Γ(S, D(x))` is injective if `U` is affine: localization is exact. -/
lemma awayLift_injective (hU : IsAffineOpen U) : Function.Injective (awayLift A x) := by
  have := hU.isLocalization_basicOpen (x : Γ(S, U))
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨y, ⟨_, n, rfl⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers x) z
  have h1 : awayLift A x (IsLocalization.mk' (Localization.Away x) y
      (⟨x ^ n, n, rfl⟩ : Submonoid.powers x)) * awayLift A x (algebraMap A _ (x ^ n)) =
      awayLift A x (algebraMap A _ y) := by
    rw [← map_mul, IsLocalization.mk'_spec]
  rw [hz, zero_mul, awayLift_algebraMap] at h1
  have h2 : algebraMap Γ(S, U) Γ(S, S.basicOpen (x : Γ(S, U))) (y : Γ(S, U)) = 0 := h1.symm
  obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (x : Γ(S, U)))
    _ _).mp h2
  rw [IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨x ^ m, m, rfl⟩, Subtype.ext ?_⟩
  simpa using hm

/-- Every section of the localization subring `A[1/x]` over `D(x)` comes from `A[1/x]`. -/
lemma mem_range_awayLift {z : Γ(S, S.basicOpen (x : Γ(S, U)))}
    (hz : z ∈ localizationSubring A (x : Γ(S, U)) (S.basicOpen (x : Γ(S, U))) le_rfl) :
    z ∈ (awayLift A x).range := by
  refine (Subring.closure_le.mpr ?_ : _ ≤ (awayLift A x).range) hz
  rintro _ (rfl | ⟨y, hy, rfl⟩)
  · refine ⟨IsLocalization.Away.invSelf x, ?_⟩
    have h1 := resLE_mul_basicOpenInv (x : Γ(S, U)) (S.basicOpen (x : Γ(S, U))) le_rfl
    have h2 : S.resLE (le_rfl.trans (S.basicOpen_le (x : Γ(S, U)))) (x : Γ(S, U)) *
        awayLift A x (IsLocalization.Away.invSelf x) = 1 := by
      rw [← awayLift_algebraMap, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
    calc awayLift A x (IsLocalization.Away.invSelf x)
        = awayLift A x (IsLocalization.Away.invSelf x) *
          (S.resLE (le_rfl.trans (S.basicOpen_le (x : Γ(S, U)))) (x : Γ(S, U)) *
            basicOpenInv (x : Γ(S, U)) (S.basicOpen (x : Γ(S, U))) le_rfl) := by
          rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, mul_comm _ (S.resLE _ _), h2, one_mul]
  · exact ⟨algebraMap A _ ⟨y, hy⟩, awayLift_algebraMap A x _⟩

/-- A ring map `R ⟶ Γ(S, D(x))` with values in `A[1/x]` factors through `A[1/x]`. -/
lemma exists_comp_awayLift (hU : IsAffineOpen U) {R : CommRingCat.{u}}
    (ρ : R ⟶ Γ(S, S.basicOpen (x : Γ(S, U))))
    (hρ : ∀ y, ρ y ∈ localizationSubring A (x : Γ(S, U)) (S.basicOpen (x : Γ(S, U))) le_rfl) :
    ∃ γ : R ⟶ CommRingCat.of (Localization.Away x), γ ≫ CommRingCat.ofHom (awayLift A x) = ρ := by
  let e := RingEquiv.ofBijective (awayLift A x).rangeRestrict
    ⟨fun a b hab ↦ awayLift_injective A x hU (congrArg Subtype.val hab),
      (awayLift A x).rangeRestrict_surjective⟩
  refine ⟨CommRingCat.ofHom (e.symm.toRingHom.comp
    (ρ.hom.codRestrict _ fun y ↦ mem_range_awayLift A x (hρ y))), ?_⟩
  ext y
  have := congrArg Subtype.val (e.apply_symm_apply ⟨ρ y, mem_range_awayLift A x (hρ y)⟩)
  exact this

variable {A x}

/-- The chart lift to `D(x)`, read through `D(x) ≅ Spec A[1/x]`, is `Spec` of `awayLift`. -/
@[reassoc]
lemma chartLift_basicOpenIsoSpecAway (h : S.basicOpen (x : Γ(S, U)) ≤ U) (hV) :
    chartLift A h (PrimeSpectrum.basicOpen x) hV ≫ (basicOpenIsoSpecAway x).hom =
      (S.basicOpen (x : Γ(S, U))).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (awayLift A x)) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (CommRingCat.of A) (Localization.Away x)))) :=
    IsOpenImmersion.of_isLocalization x
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom
    (algebraMap (CommRingCat.of A) (Localization.Away x)))), Category.assoc,
    basicOpenIsoSpecAway_hom_SpecMap, chartLift_ι, Category.assoc, ← Spec.map_comp,
    ofHom_algebraMap_comp_awayLift]
  rfl

lemma exists_eq_basicOpenIsoSpecAway_hom_comp {R : CommRingCat.{u}}
    (f : (PrimeSpectrum.basicOpen x : (Spec (CommRingCat.of A)).Opens).toScheme ⟶ Spec R) :
    ∃ γ : R ⟶ CommRingCat.of (Localization.Away x),
      f = (basicOpenIsoSpecAway x).hom ≫ Spec.map γ :=
  ⟨Spec.preimage ((basicOpenIsoSpecAway x).inv ≫ f), by rw [Spec.map_preimage,
    Iso.hom_inv_id_assoc]⟩

/-- A morphism `D(x) ⟶ Spec R` whose restriction along the chart lift is induced by `ρ` is
`Spec` of a ring map `γ` with `awayLift ∘ γ = ρ`. -/
lemma comp_awayLift_eq (hU : IsAffineOpen U) (h : S.basicOpen (x : Γ(S, U)) ≤ U) (hV)
    {R : CommRingCat.{u}} (γ : R ⟶ CommRingCat.of (Localization.Away x))
    (ρ : R ⟶ Γ(S, S.basicOpen (x : Γ(S, U))))
    (hγ : chartLift A h (PrimeSpectrum.basicOpen x) hV ≫ (basicOpenIsoSpecAway x).hom ≫
      Spec.map γ = (S.basicOpen (x : Γ(S, U))).toSpecΓ ≫ Spec.map ρ) :
    γ ≫ CommRingCat.ofHom (awayLift A x) = ρ := by
  rw [chartLift_basicOpenIsoSpecAway_assoc, ← Spec.map_comp] at hγ
  exact toSpecΓ_SpecMap_injective (hU.basicOpen _) hγ

/-- Morphisms out of `D(x) ⊆ Spec A` into an affine scheme are determined by their restriction
along the chart lift. -/
lemma chartLift_basicOpen_cancel (hU : IsAffineOpen U) {V : (Spec (CommRingCat.of A)).Opens}
    (hV : V = PrimeSpectrum.basicOpen x) {W : S.Opens} (hW : W = S.basicOpen (x : Γ(S, U)))
    (h : W ≤ U) (hr) {R : CommRingCat.{u}} (f g : V.toScheme ⟶ Spec R)
    (hfg : chartLift A h V hr ≫ f = chartLift A h V hr ≫ g) : f = g := by
  subst hV hW
  obtain ⟨γ, rfl⟩ := exists_eq_basicOpenIsoSpecAway_hom_comp f
  obtain ⟨δ, rfl⟩ := exists_eq_basicOpenIsoSpecAway_hom_comp g
  rw [chartLift_basicOpenIsoSpecAway_assoc, chartLift_basicOpenIsoSpecAway_assoc,
    ← Spec.map_comp, ← Spec.map_comp] at hfg
  have h2 := toSpecΓ_SpecMap_injective (hU.basicOpen _) hfg
  have : γ = δ := by
    ext y
    exact awayLift_injective A x hU (ConcreteCategory.congr_hom h2 y)
  rw [this]

end BasicOpen

/-! ### Finite unions of basic opens -/

section iSup

variable {A : Subring Γ(S, U)} {σ : Type*} (k : σ → A)

/-- Morphisms out of `⋃ᵢ D(kᵢ) ⊆ Spec A` into an affine scheme are determined by their
restriction along the chart lift from `⋃ᵢ D_S(kᵢ) ⊆ S`. -/
lemma chartLift_cancel (hU : IsAffineOpen U) {V : (Spec (CommRingCat.of A)).Opens}
    (hV : V = ⨆ i, PrimeSpectrum.basicOpen (k i)) {W : S.Opens}
    (hW : W = ⨆ i, S.basicOpen (k i : Γ(S, U))) (h : W ≤ U) (hr) {R : CommRingCat.{u}}
    (f g : V.toScheme ⟶ Spec R) (hfg : chartLift A h V hr ≫ f = chartLift A h V hr ≫ g) :
    f = g := by
  subst hV hW
  refine (Scheme.Opens.iSupOpenCover _).hom_ext _ _ fun i ↦ ?_
  have hle : S.basicOpen (k i : Γ(S, U)) ≤ ⨆ i, S.basicOpen (k i : Γ(S, U)) :=
    le_iSup (fun i ↦ S.basicOpen (k i : Γ(S, U))) i
  have hr' := range_subringChart_subset_basicOpen A (hle.trans h) (k i) le_rfl
  refine chartLift_basicOpen_cancel hU rfl rfl (hle.trans h) hr' _ _ ?_
  have e := homOfLE_chartLift A h hle (le_iSup (fun i ↦ PrimeSpectrum.basicOpen (k i)) i) hr hr'
  change chartLift A _ _ hr' ≫ (Spec _).homOfLE _ ≫ f =
    chartLift A _ _ hr' ≫ (Spec _).homOfLE _ ≫ g
  rw [← reassoc_of% e, ← reassoc_of% e, hfg]

/-- A morphism `⋃ᵢ D_S(kᵢ) ⟶ Spec R` induced by a ring map `ρ` whose restrictions to the
`D_S(kᵢ)` take values in the localization subrings `A[1/kᵢ]` extends along the chart lift to
`⋃ᵢ D(kᵢ) ⊆ Spec A`. -/
lemma exists_chartLift_comp_eq (hU : IsAffineOpen U) {V : (Spec (CommRingCat.of A)).Opens}
    (hV : V = ⨆ i, PrimeSpectrum.basicOpen (k i)) {W : S.Opens}
    (hW : W = ⨆ i, S.basicOpen (k i : Γ(S, U))) (h : W ≤ U) (hr) {R : CommRingCat.{u}}
    (ρ : R ⟶ Γ(S, W))
    (hρ : ∀ i y (hi : S.basicOpen (k i : Γ(S, U)) ≤ W), S.resLE hi (ρ y) ∈
      localizationSubring A (k i : Γ(S, U)) (S.basicOpen (k i : Γ(S, U))) le_rfl) :
    ∃ f : V.toScheme ⟶ Spec R, chartLift A h V hr ≫ f = W.toSpecΓ ≫ Spec.map ρ := by
  subst hV hW
  have hle (i : σ) : S.basicOpen (k i : Γ(S, U)) ≤ ⨆ i, S.basicOpen (k i : Γ(S, U)) :=
    le_iSup (fun i ↦ S.basicOpen (k i : Γ(S, U))) i
  have hr' (i : σ) := range_subringChart_subset_basicOpen A ((hle i).trans h) (k i) le_rfl
  choose γ hγ using fun i ↦ exists_comp_awayLift A (k i) hU (ρ ≫ S.resLE (hle i))
    fun y ↦ hρ i y (hle i)
  -- the local extensions
  let f (i : σ) := (basicOpenIsoSpecAway (k i)).hom ≫ Spec.map (γ i)
  have hf (i : σ) : chartLift A ((hle i).trans h) _ (hr' i) ≫ f i =
      (S.basicOpen (k i : Γ(S, U))).toSpecΓ ≫ Spec.map (ρ ≫ S.resLE (hle i)) := by
    rw [chartLift_basicOpenIsoSpecAway_assoc, ← Spec.map_comp, hγ]
  have hcompat (i j : σ) : (Spec (CommRingCat.of A)).homOfLE inf_le_left ≫ f i =
      (Spec (CommRingCat.of A)).homOfLE inf_le_right ≫ f j := by
    have hij : S.basicOpen ((k i * k j : A) : Γ(S, U)) ≤ U :=
      S.basicOpen_le _
    have hr'' := range_subringChart_subset_basicOpen A hij (k i * k j) le_rfl
    have hVij : PrimeSpectrum.basicOpen (k i) ⊓ PrimeSpectrum.basicOpen (k j) =
        PrimeSpectrum.basicOpen (k i * k j) := (PrimeSpectrum.basicOpen_mul _ _).symm
    have hWi : S.basicOpen ((k i * k j : A) : Γ(S, U)) ≤ S.basicOpen (k i : Γ(S, U)) := by
      rw [Subring.coe_mul, Scheme.basicOpen_mul]
      exact inf_le_left
    have hWj : S.basicOpen ((k i * k j : A) : Γ(S, U)) ≤ S.basicOpen (k j : Γ(S, U)) := by
      rw [Subring.coe_mul, Scheme.basicOpen_mul]
      exact inf_le_right
    refine chartLift_basicOpen_cancel hU hVij rfl hij
      (by rw [hVij]; exact hr'') _ _ ?_
    rw [← homOfLE_chartLift_assoc A ((hle i).trans h) hWi inf_le_left (hr' i),
      ← homOfLE_chartLift_assoc A ((hle j).trans h) hWj inf_le_right (hr' j), hf, hf,
      homOfLE_toSpecΓ_SpecMap, homOfLE_toSpecΓ_SpecMap, Category.assoc, Category.assoc,
      resLE_comp, resLE_comp]
  let F := (Scheme.Opens.iSupOpenCover fun i ↦ PrimeSpectrum.basicOpen (k i)).glueMorphisms f
    fun i j ↦ by
      have hP := isPullback_opens_inf_le
        (le_iSup (fun i ↦ PrimeSpectrum.basicOpen (k i)) i)
        (le_iSup (fun i ↦ PrimeSpectrum.basicOpen (k i)) j)
      change pullback.fst ((Spec (CommRingCat.of A)).homOfLE _)
          ((Spec (CommRingCat.of A)).homOfLE _) ≫ f i =
        pullback.snd ((Spec (CommRingCat.of A)).homOfLE _)
          ((Spec (CommRingCat.of A)).homOfLE _) ≫ f j
      rw [← hP.isoPullback_inv_fst, ← hP.isoPullback_inv_snd, Category.assoc, Category.assoc,
        hcompat]
  refine ⟨F, (Scheme.Opens.iSupOpenCover _).hom_ext _ _ fun i ↦ ?_⟩
  have e := homOfLE_chartLift A h (hle i) (le_iSup (fun i ↦ PrimeSpectrum.basicOpen (k i)) i)
    hr (hr' i)
  have hι := (Scheme.Opens.iSupOpenCover fun i ↦ PrimeSpectrum.basicOpen (k i)).ι_glueMorphisms
    f _ i
  change S.homOfLE (hle i) ≫ chartLift A h _ hr ≫ F = S.homOfLE (hle i) ≫ _
  rw [reassoc_of% e]
  change chartLift A _ _ (hr' i) ≫ (Scheme.Opens.iSupOpenCover _).f i ≫ F = _
  rw [hι, hf, homOfLE_toSpecΓ_SpecMap]

/-- Image criterion: if `τ : ⋃ᵢ D(kᵢ) ⟶ Spec A'` extends the chart map of a subring
`A' ⊆ Γ(S, U')`, and on every `D_S(kᵢ)` the restrictions of finitely many `k' q ∈ A'` generate the
unit ideal of `A[1/kᵢ]`, then `τ` lands in `⋃_q D(k' q)`. -/
lemma range_subset_iSup_basicOpen (hU : IsAffineOpen U) {V : (Spec (CommRingCat.of A)).Opens}
    (hV : V = ⨆ i, PrimeSpectrum.basicOpen (k i)) {W : S.Opens}
    (hW : W = ⨆ i, S.basicOpen (k i : Γ(S, U))) (h : W ≤ U) (hr) {U' : S.Opens}
    {A' : Subring Γ(S, U')} (hWU' : W ≤ U') (τ : V.toScheme ⟶ Spec (CommRingCat.of A'))
    (hτ : chartLift A h V hr ≫ τ = subringChart A' hWU') {κ : Type*} [Fintype κ] (k' : κ → A')
    (hunit : ∀ i (hi : S.basicOpen (k i : Γ(S, U)) ≤ U'),
      ∃ e : κ → Γ(S, S.basicOpen (k i : Γ(S, U))),
        (∀ q, e q ∈ localizationSubring A (k i : Γ(S, U)) (S.basicOpen (k i : Γ(S, U))) le_rfl) ∧
        ∑ q, e q * S.resLE hi (k' q : Γ(S, U')) = 1) :
    Set.range τ ⊆ ((⨆ q, PrimeSpectrum.basicOpen (k' q) :
      (Spec (CommRingCat.of A')).Opens) : Set (Spec (CommRingCat.of A'))) := by
  subst hV hW
  rintro _ ⟨p, rfl⟩
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp p.2
  have hle : S.basicOpen (k i : Γ(S, U)) ≤ ⨆ i, S.basicOpen (k i : Γ(S, U)) :=
    le_iSup (fun i ↦ S.basicOpen (k i : Γ(S, U))) i
  have hVle := le_iSup (fun i ↦ PrimeSpectrum.basicOpen (k i)) i
  have hr' := range_subringChart_subset_basicOpen A (hle.trans h) (k i) le_rfl
  obtain ⟨γ, hγ⟩ := exists_eq_basicOpenIsoSpecAway_hom_comp
    ((Spec (CommRingCat.of A)).homOfLE hVle ≫ τ)
  have hγ' : γ ≫ CommRingCat.ofHom (awayLift A (k i)) = subringRes A' (hle.trans hWU') := by
    refine comp_awayLift_eq hU (hle.trans h) hr' γ _ ?_
    rw [← hγ, ← homOfLE_chartLift_assoc A h hle hVle hr hr', hτ, homOfLE_subringChart]
    rfl
  obtain ⟨e, he, hsum⟩ := hunit i (hle.trans hWU')
  choose e' he' using fun q ↦ mem_range_awayLift A (k i) (he q)
  have hsum' : ∑ q, e' q * γ (k' q) = 1 := by
    apply awayLift_injective A (k i) hU
    rw [map_sum, map_one, ← hsum]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [map_mul, he']
    congr 1
    exact (ConcreteCategory.congr_hom hγ' (k' q))
  have hspan : Ideal.span (Set.range fun q ↦ γ (k' q)) = ⊤ := by
    rw [Ideal.eq_top_iff_one, ← hsum']
    exact Ideal.sum_mem _ fun q _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨q, rfl⟩)
  have htop := PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr hspan
  set p' : (PrimeSpectrum.basicOpen (k i) : (Spec (CommRingCat.of A)).Opens).toScheme :=
    ⟨p.1, hi⟩
  have hpp' : (Spec (CommRingCat.of A)).homOfLE hVle p' = p := Subtype.ext rfl
  have hmem : (basicOpenIsoSpecAway (k i)).hom p' ∈
      (⨆ q, PrimeSpectrum.basicOpen (γ (k' q)) :
        (Spec (CommRingCat.of (Localization.Away (k i)))).Opens) := by
    rw [htop]
    trivial
  obtain ⟨q, hq⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨q, ?_⟩
  have : τ p = Spec.map γ ((basicOpenIsoSpecAway (k i)).hom p') := by
    rw [← hpp', ← Scheme.Hom.comp_apply, hγ, Scheme.Hom.comp_apply]
  rw [this]
  exact hq

end iSup

end AlgebraicGeometry.Scheme
