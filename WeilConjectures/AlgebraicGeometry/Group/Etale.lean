/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.AlgebraicGeometry.Group.Infinitesimal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-!
# The `n`-th power endomorphism of a commutative group scheme is étale

Let `G` be a commutative group scheme over a field `K` and let `n` be a natural number which is
invertible in `K`. This file shows that the `n`-th power endomorphism `[n] : G ⟶ G` is
formally unramified, and that it is smooth, hence étale, as soon as `G` is smooth over `K`.
No properness is needed, so this holds well beyond abelian varieties.

Both statements are checked on affine charts: writing `f := [n]` and `ρ := f.appLE U V e` for
affine opens `V ⊆ f ⁻¹ᵁ U` of `G`, one has to show that `ρ` is formally unramified, resp.
smooth. An `R`-algebra map out of `Γ(G, V)` into a `K`-algebra `B` is the same thing as a
`B`-point of `G` landing in `V` whose `n`-th power is a prescribed `B`-point landing in `U`, so
both statements turn into statements about the group of `B`-points of `G` which are trivial on
the square-zero thickening `Spec (B ⧸ I) ⊆ Spec B`:

* injectivity of the lifts (formal unramifiedness) is *rigidity* of that group, i.e.
  `AlgebraicGeometry.GrpObj.eq_one_of_pow_eq_one`;
* existence of the lifts (formal smoothness) is the `n`-*divisibility* of that group, i.e.
  `AlgebraicGeometry.GrpObj.exists_pow_eq`, applied to correct an arbitrary lift over `K`,
  which exists because `G` is smooth over `K`.

Finite presentation of `ρ` is not group theory at all: it is cancellation of the structure map
`K ⟶ Γ(G, U)` out of the finitely presented `K ⟶ Γ(G, V)`.

Mathlib has no file on group schemes over a field, so this file is not a mirror of any Mathlib
file and lives outside `WeilConjectures/Mathlib/`.

## Main statements

- `AlgebraicGeometry.GrpObj.formallyUnramified_npow_left`: the `n`-th power endomorphism of a
  commutative group scheme over `K` is formally unramified if `n` is invertible in `K`.
- `AlgebraicGeometry.GrpObj.smooth_npow_left`: it is smooth if moreover `G` is smooth over `K`.
- `AlgebraicGeometry.GrpObj.etale_npow_left`: hence it is étale.

## Blueprint

`formallyUnramified_npow_left` is `thm:av-mulby-formally-unramified`, `smooth_npow_left` is
`thm:av-mulby-formally-smooth` together with `lem:av-mulby-lfp`, and `etale_npow_left` is
`thm:av-mulby-etale`, all of the chapter on the multiplication-by-`n` isogeny of an abelian
variety; the statements here need neither properness nor integrality of `G`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

open scoped MonObj

namespace AlgebraicGeometry.GrpObj

variable {K : Type u} [Field K] {G : Over (Spec (.of K))} [GrpObj G] {U V : G.left.Opens}
  {n : ℕ}

/-! ### Points of `G` in an affine chart

A `B`-point of `G` landing in an affine open `U` of `G` is the same thing as a `K`-algebra map
`Γ(G, U) ⟶ B`. -/

section Chart

/-- The structure ring map `K ⟶ Γ(G, U)` of an affine open `U` of a `K`-scheme `G`. -/
private noncomputable def baseHom (hU : IsAffineOpen U) : CommRingCat.of K ⟶ Γ(G.left, U) :=
  Spec.preimage (hU.fromSpec ≫ G.hom)

omit [GrpObj G] in
private lemma Spec_map_baseHom (hU : IsAffineOpen U) :
    Spec.map (baseHom hU) = hU.fromSpec ≫ G.hom :=
  Spec.map_preimage _

variable {B : CommRingCat.{u}} {t : Spec B ⟶ Spec (.of K)}

omit [GrpObj G] in
/-- A ring map `Γ(G, U) ⟶ B` compatible with the structure maps to `K` is a `B`-point of `G`. -/
private noncomputable def ptOfHom (hU : IsAffineOpen U) (φ : Γ(G.left, U) ⟶ B)
    (t : Spec B ⟶ Spec (.of K)) (h : baseHom hU ≫ φ = Spec.preimage t) : Over.mk t ⟶ G :=
  Over.homMk (Spec.map φ ≫ hU.fromSpec) (by
    rw [Category.assoc, ← Spec_map_baseHom hU, ← Spec.map_comp, h, Spec.map_preimage]
    rfl)

omit [GrpObj G] in
private lemma ptOfHom_left (hU : IsAffineOpen U) (φ : Γ(G.left, U) ⟶ B)
    (h : baseHom hU ≫ φ = Spec.preimage t) :
    (ptOfHom hU φ t h).left = Spec.map φ ≫ hU.fromSpec :=
  rfl

omit [GrpObj G] in
private lemma range_ptOfHom (hU : IsAffineOpen U) (φ : Γ(G.left, U) ⟶ B)
    (h : baseHom hU ≫ φ = Spec.preimage t) :
    Set.range (ptOfHom hU φ t h).left ⊆ (U : Set G.left) := by
  rw [ptOfHom_left]
  refine Set.Subset.trans ?_ hU.range_fromSpec.le
  simpa using Set.range_comp_subset_range (Spec.map φ).base hU.fromSpec.base

omit [GrpObj G] in
private lemma app_ptOfHom (hU : IsAffineOpen U) (φ : Γ(G.left, U) ⟶ B)
    (h : baseHom hU ≫ φ = Spec.preimage t) :
    hU.app (ptOfHom hU φ t h).left (range_ptOfHom hU φ h) = φ :=
  hU.app_eq _ _ _ rfl

/-- The structure maps of two affine charts of `G` are compatible with the ring map induced by
the `n`-th power endomorphism. -/
private lemma baseHom_comp_appLE (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : V ≤ (GrpObj.npow G n).left ⁻¹ᵁ U) :
    baseHom hU ≫ (GrpObj.npow G n).left.appLE U V e = baseHom hV := by
  refine Spec.map_injective ?_
  rw [Spec.map_comp, Spec_map_baseHom, Spec_map_baseHom, ← Category.assoc,
    IsAffineOpen.SpecMap_appLE_fromSpec _ hU hV e, Category.assoc, Over.w]

/-- If a `B`-point of `G` lands in `V`, its `n`-th power lands in `U`. -/
private lemma range_npow_left (e : V ≤ (GrpObj.npow G n).left ⁻¹ᵁ U) (x : Over.mk t ⟶ G)
    (hx : Set.range x.left ⊆ (V : Set G.left)) :
    Set.range (x ^ n).left ⊆ (U : Set G.left) := by
  rw [← GrpObj.comp_npow, Over.comp_left]
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Hom.comp_apply]
  exact e (hx ⟨y, rfl⟩)

/-- On functions, taking the `n`-th power of a `B`-point of `G` landing in `V` is composition
with the ring map induced by the `n`-th power endomorphism. -/
private lemma app_npow_left (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : V ≤ (GrpObj.npow G n).left ⁻¹ᵁ U) (x : Over.mk t ⟶ G)
    (hx : Set.range x.left ⊆ (V : Set G.left)) :
    hU.app (x ^ n).left (range_npow_left e x hx)
      = (GrpObj.npow G n).left.appLE U V e ≫ hV.app x.left hx := by
  refine hU.app_eq _ _ _ ?_
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec _ hU hV,
    ← Category.assoc, IsAffineOpen.Spec_map_app, ← Over.comp_left, GrpObj.comp_npow]

end Chart

/-! ### The two group theoretic inputs, in a chart

Both halves of the proof are statements about the ring maps `Γ(G, V) ⟶ B` lifting a fixed
ring map `Γ(G, U) ⟶ B` along the `n`-th power endomorphism, which via the dictionary above are
statements about `n`-th roots of a fixed `B`-point of `G`. -/

section Group

variable [IsCommMonObj G] (hU : IsAffineOpen U) (hV : IsAffineOpen V)
  (e : V ≤ (GrpObj.npow G n).left ⁻¹ᵁ U) {B : CommRingCat.{u}} {I : Ideal B}

include hU hV e in
/-- **Rigidity in a chart.** Two ring maps `Γ(G, V) ⟶ B` inducing the same ring map on `Γ(G, U)`
along the `n`-th power endomorphism and agreeing modulo a square-zero ideal `I` are equal, if
`n` is invertible in `K`. -/
private lemma eq_of_appLE_comp_eq (hI : I ^ 2 = ⊥) (hn : (n : K) ≠ 0)
    (α : Γ(G.left, U) ⟶ B) (φ ψ : Γ(G.left, V) ⟶ B)
    (hφ : (GrpObj.npow G n).left.appLE U V e ≫ φ = α)
    (hψ : (GrpObj.npow G n).left.appLE U V e ≫ ψ = α)
    (h : φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)
      = ψ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)) :
    φ = ψ := by
  set t : Spec B ⟶ Spec (.of K) := Spec.map (baseHom hU ≫ α) with ht
  have hb : ∀ χ : Γ(G.left, V) ⟶ B, (GrpObj.npow G n).left.appLE U V e ≫ χ = α →
      baseHom hV ≫ χ = Spec.preimage t := fun χ hχ ↦ by
    rw [ht, Spec.preimage_map, ← baseHom_comp_appLE hU hV e, Category.assoc, hχ]
  have hpow : ∀ (χ : Γ(G.left, V) ⟶ B) (hχ : (GrpObj.npow G n).left.appLE U V e ≫ χ = α),
      ((ptOfHom hV χ t (hb χ hχ)) ^ n).left = Spec.map α ≫ hU.fromSpec := fun χ hχ ↦ by
    rw [← IsAffineOpen.Spec_map_app hU _
      (range_npow_left e _ (range_ptOfHom hV χ (hb χ hχ))),
      app_npow_left hU hV e _ (range_ptOfHom hV χ (hb χ hχ)), app_ptOfHom, hχ]
  have hthick : Spec.overQuotientMk I t ≫ ptOfHom hV φ t (hb φ hφ)
      = Spec.overQuotientMk I t ≫ ptOfHom hV ψ t (hb ψ hψ) := by
    refine Over.OverMorphism.ext ?_
    rw [Over.comp_left, Over.comp_left, Spec.overQuotientMk_left, ptOfHom_left, ptOfHom_left,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, h]
  have hd : Spec.overQuotientMk I t
      ≫ ((ptOfHom hV φ t (hb φ hφ))⁻¹ * ptOfHom hV ψ t (hb ψ hψ)) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, hthick, inv_mul_cancel]
  have hdn : ((ptOfHom hV φ t (hb φ hφ))⁻¹ * ptOfHom hV ψ t (hb ψ hψ)) ^ n = 1 := by
    rw [mul_pow, inv_pow, inv_mul_eq_one]
    exact Over.OverMorphism.ext (by rw [hpow φ hφ, hpow ψ hψ])
  have hxy : ptOfHom hV φ t (hb φ hφ) = ptOfHom hV ψ t (hb ψ hψ) := by
    have := GrpObj.eq_one_of_pow_eq_one hI hn _ hd hdn
    rwa [inv_mul_eq_one] at this
  exact Spec.map_injective ((cancel_mono hV.fromSpec).mp congr(($hxy).left))

include hU hV e in
/-- **Divisibility in a chart.** A ring map `Γ(G, V) ⟶ B ⧸ I` compatible with the `n`-th power
endomorphism, `I` square-zero, lifts to a compatible ring map `Γ(G, V) ⟶ B` as soon as it lifts
to some ring map over `K`, if `n` is invertible in `K`. -/
private lemma exists_appLE_comp_eq (hI : I ^ 2 = ⊥) (hn : (n : K) ≠ 0)
    (α : Γ(G.left, U) ⟶ B) (σ₀ : Γ(G.left, V) ⟶ CommRingCat.of (B ⧸ I))
    (hσ₀ : (GrpObj.npow G n).left.appLE U V e ≫ σ₀
      = α ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))
    (σ₁ : Γ(G.left, V) ⟶ B) (hσ₁ : baseHom hV ≫ σ₁ = baseHom hU ≫ α)
    (hσ : σ₁ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) = σ₀) :
    ∃ σ : Γ(G.left, V) ⟶ B, (GrpObj.npow G n).left.appLE U V e ≫ σ = α ∧
      σ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) = σ₀ := by
  set t : Spec B ⟶ Spec (.of K) := Spec.map (baseHom hU ≫ α) with ht
  have hb1 : baseHom hV ≫ σ₁ = Spec.preimage t := by rw [ht, Spec.preimage_map, hσ₁]
  have hbα : baseHom hU ≫ α = Spec.preimage t := by rw [ht, Spec.preimage_map]
  set x₁ := ptOfHom hV σ₁ t hb1 with hx₁
  set y := ptOfHom hU α t hbα with hy
  have hring : ((GrpObj.npow G n).left.appLE U V e ≫ σ₁)
      ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)
      = α ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
    rw [Category.assoc, hσ, hσ₀]
  have h1 : Spec.overQuotientMk I t ≫ x₁ ^ n = Spec.overQuotientMk I t ≫ y := by
    refine Over.OverMorphism.ext ?_
    have hl : (x₁ ^ n).left
        = Spec.map ((GrpObj.npow G n).left.appLE U V e ≫ σ₁) ≫ hU.fromSpec := by
      rw [← IsAffineOpen.Spec_map_app hU _
          (range_npow_left e _ (range_ptOfHom hV σ₁ hb1)),
        app_npow_left hU hV e _ (range_ptOfHom hV σ₁ hb1), app_ptOfHom]
    rw [Over.comp_left, Over.comp_left, Spec.overQuotientMk_left, hl, hy, ptOfHom_left,
      ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hring]
  have hd : Spec.overQuotientMk I t ≫ ((x₁ ^ n)⁻¹ * y) = 1 := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, h1, inv_mul_cancel]
  obtain ⟨c, hc1, hc2⟩ := GrpObj.exists_pow_eq hI hn _ hd
  have hxn : (x₁ * c) ^ n = y := by rw [mul_pow, hc2, mul_inv_cancel_left]
  have hqx : Spec.overQuotientMk I t ≫ (x₁ * c) = Spec.overQuotientMk I t ≫ x₁ := by
    rw [MonObj.comp_mul, hc1, mul_one]
  have hqxl : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ (x₁ * c).left
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ x₁.left := by
    have := congr(($hqx).left)
    rwa [Over.comp_left, Over.comp_left, Spec.overQuotientMk_left] at this
  have hnil : I ≤ nilradical B := fun z hz ↦
    ⟨2, by simpa [hI] using Ideal.pow_mem_pow hz 2⟩
  have hrange : Set.range (x₁ * c).left ⊆ (V : Set G.left) := by
    have hsurj : Function.Surjective
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base :=
      (PrimeSpectrum.comap_quotientMk_bijective_of_le_nilradical hnil).surjective
    rintro _ ⟨y₀, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj y₀
    have hz : (x₁ * c).left ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base z)
        = x₁.left ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).base z) :=
      (Scheme.Hom.comp_apply _ _ z).symm.trans
        ((congr(($hqxl) z)).trans (Scheme.Hom.comp_apply _ _ z))
    rw [hz]
    exact range_ptOfHom hV σ₁ hb1 ⟨_, rfl⟩
  refine ⟨hV.app (x₁ * c).left hrange, ?_, ?_⟩
  · have happ : hU.app ((x₁ * c) ^ n).left (range_npow_left e _ hrange) = α :=
      hU.app_eq _ _ _ congr(($hxn).left).symm
    exact (app_npow_left hU hV e _ hrange).symm.trans happ
  · refine Spec.map_injective ((cancel_mono hV.fromSpec).mp ?_)
    rw [Spec.map_comp, Category.assoc, IsAffineOpen.Spec_map_app, hqxl, hx₁, ptOfHom_left,
      ← Spec.map_comp_assoc, hσ]

end Group

/-! ### Smoothness of the affine charts -/

section Smooth

variable [Smooth G.hom]

omit [GrpObj G] in
/-- The structure map of an affine chart of a smooth `K`-scheme is a smooth ring map. -/
private lemma smooth_baseHom (hU : IsAffineOpen U) : RingHom.Smooth (baseHom hU).hom := by
  rw [← HasRingHomProperty.Spec_iff (P := @Smooth), Spec_map_baseHom]
  infer_instance

omit [GrpObj G] in
/-- The structure map of an affine chart of a smooth `K`-scheme is of finite type. -/
private lemma finiteType_baseHom (hU : IsAffineOpen U) :
    RingHom.FiniteType (baseHom hU).hom := by
  rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType), Spec_map_baseHom]
  infer_instance

end Smooth

/-! ### The main statements -/

variable [IsCommMonObj G]

/-- **The `n`-th power endomorphism of a commutative group scheme over a field `K` is formally
unramified** if `n` is invertible in `K`. -/
theorem formallyUnramified_npow_left (hn : (n : K) ≠ 0) :
    FormallyUnramified (GrpObj.npow G n).left := by
  rw [HasRingHomProperty.iff_appLE (P := @FormallyUnramified)]
  intro U V e
  algebraize [((GrpObj.npow G n).left.appLE U.1 V.1 e).hom]
  change Algebra.FormallyUnramified _ _
  rw [Algebra.FormallyUnramified.iff_comp_injective]
  intro B _ _ I hI a b hab
  have hcomm : ∀ c : ↥Γ(G.left, V.1) →ₐ[↥Γ(G.left, U.1)] B,
      (GrpObj.npow G n).left.appLE U.1 V.1 e ≫ CommRingCat.ofHom c.toRingHom
        = CommRingCat.ofHom (algebraMap ↥Γ(G.left, U.1) B) :=
    fun c ↦ CommRingCat.hom_ext (RingHom.ext fun r ↦ c.commutes r)
  have key := eq_of_appLE_comp_eq U.2 V.2 e hI hn (CommRingCat.ofHom (algebraMap _ B))
    (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom) (hcomm a) (hcomm b)
    (CommRingCat.hom_ext (RingHom.ext fun s ↦ AlgHom.congr_fun hab s))
  exact AlgHom.ext fun s ↦ congr(($key).hom s)

/-- **The `n`-th power endomorphism of a smooth commutative group scheme over a field `K` is
smooth** if `n` is invertible in `K`. -/
theorem smooth_npow_left [Smooth G.hom] (hn : (n : K) ≠ 0) :
    Smooth (GrpObj.npow G n).left := by
  rw [HasRingHomProperty.iff_appLE (P := @Smooth)]
  intro U V e
  rw [RingHom.smooth_def]
  have hfp : ((GrpObj.npow G n).left.appLE U.1 V.1 e).hom.comp (baseHom U.2).hom
      = (baseHom V.2).hom := by
    rw [← CommRingCat.hom_comp, baseHom_comp_appLE]
  refine ⟨?_, ?_⟩
  · -- formal smoothness
    algebraize [((GrpObj.npow G n).left.appLE U.1 V.1 e).hom]
    change Algebra.FormallySmooth _ _
    apply Algebra.FormallySmooth.of_comp_surjective
    intro B _ _ I hI σ₀
    set α : Γ(G.left, U.1) ⟶ CommRingCat.of B :=
      CommRingCat.ofHom (algebraMap ↥Γ(G.left, U.1) B)
    set σ₀' : Γ(G.left, V.1) ⟶ CommRingCat.of (B ⧸ I) :=
      CommRingCat.ofHom σ₀.toRingHom
    have hσ₀ : (GrpObj.npow G n).left.appLE U.1 V.1 e ≫ σ₀'
        = α ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) :=
      CommRingCat.hom_ext (RingHom.ext fun r ↦ σ₀.commutes r)
    let _ : Algebra K ↥Γ(G.left, V.1) := (baseHom V.2).hom.toAlgebra
    let _ : Algebra K B := (baseHom U.2 ≫ α).hom.toAlgebra
    have hfs : Algebra.FormallySmooth K ↥Γ(G.left, V.1) :=
      (smooth_baseHom V.2).formallySmooth
    have hbase : baseHom V.2 ≫ σ₀' = (baseHom U.2 ≫ α)
        ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) := by
      rw [← baseHom_comp_appLE U.2 V.2 e, Category.assoc, hσ₀, Category.assoc]
    let σ₀'' : ↥Γ(G.left, V.1) →ₐ[K] B ⧸ I :=
      { σ₀.toRingHom with commutes' := fun k ↦ congr(($hbase).hom k) }
    obtain ⟨σ₁', hσ₁'⟩ := Algebra.FormallySmooth.comp_surjective K ↥Γ(G.left, V.1) I hI σ₀''
    set σ₁ : Γ(G.left, V.1) ⟶ CommRingCat.of B := CommRingCat.ofHom σ₁'.toRingHom
    have hσ₁ : baseHom V.2 ≫ σ₁ = baseHom U.2 ≫ α :=
      CommRingCat.hom_ext (RingHom.ext fun k ↦ σ₁'.commutes k)
    have hσ : σ₁ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I) = σ₀' :=
      CommRingCat.hom_ext (RingHom.ext fun x ↦ congr($hσ₁' x))
    obtain ⟨σ, hσα, hσmk⟩ :=
      exists_appLE_comp_eq U.2 V.2 e hI hn α σ₀' hσ₀ σ₁ hσ₁ hσ
    refine ⟨{ σ.hom with commutes' := fun r ↦ congr(($hσα).hom r) }, ?_⟩
    exact AlgHom.ext fun x ↦ congr(($hσmk).hom x)
  · -- finite presentation
    refine RingHom.FinitePresentation.of_comp_finiteType (baseHom U.2).hom ?_
      (finiteType_baseHom U.2)
    rw [hfp]
    exact (smooth_baseHom V.2).finitePresentation

/-- **The `n`-th power endomorphism of a smooth commutative group scheme over a field `K` is
étale** if `n` is invertible in `K`. -/
theorem etale_npow_left [Smooth G.hom] (hn : (n : K) ≠ 0) :
    Etale (GrpObj.npow G n).left := by
  have := smooth_npow_left (G := G) (n := n) hn
  have := formallyUnramified_npow_left (G := G) (n := n) hn
  exact Etale.of_formallyUnramified_of_flat _

end AlgebraicGeometry.GrpObj
