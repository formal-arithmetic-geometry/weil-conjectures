/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
# Morphisms into `Proj` from global sections

We record `AlgebraicGeometry.Proj.basicOpen_add_le`, the analogue for `Proj.basicOpen`
of `AlgebraicGeometry.Scheme.basicOpen_add_le`: `D₊(f + g) ⊆ D₊(f) ∪ D₊(g)`.

The main results are the following complements to
`AlgebraicGeometry.Proj.fromOfGlobalSections`, the morphism `X ⟶ Proj 𝒜` associated to a
ring homomorphism `f : A →+* Γ(X, ⊤)` whose image of the irrelevant ideal generates the
unit ideal:

- `AlgebraicGeometry.Proj.comp_fromOfGlobalSections`: naturality in `X`, i.e.
  `g ≫ fromOfGlobalSections 𝒜 f hf = fromOfGlobalSections 𝒜 (Γ(g) ∘ f) hf'`;
- `AlgebraicGeometry.Proj.fromOfGlobalSections_eq_of_eq_unit_pow_mul`: the morphism only
  depends on `f` up to rescaling by a unit, i.e. it is unchanged if `f` is replaced by
  `a ↦ uᵈ * f a` for `a` homogeneous of degree `d` and a fixed unit `u : Γ(X, ⊤)ˣ`;
- `AlgebraicGeometry.Proj.fromOfGlobalSections_eq_toSpecΓ_awayι` and
  `AlgebraicGeometry.Proj.fromOfGlobalSections_eq_awayι`: if `f t` is a unit for some
  homogeneous `t` of positive degree, the morphism factors through the affine chart
  `Spec (A_t)₀ ⟶ Proj 𝒜` via `HomogeneousLocalization.Away.lift`.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

variable {σ : Type u} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The basic open of a sum is covered by the basic opens of the summands:
`D₊(f + g) ⊆ D₊(f) ∪ D₊(g)`. -/
lemma Proj.basicOpen_add_le (f g : A) :
    Proj.basicOpen 𝒜 (f + g) ≤ Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g := by
  intro x hx
  rw [Proj.mem_basicOpen] at hx
  rw [TopologicalSpace.Opens.mem_sup, Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_contra h
  rw [not_or, not_not, not_not] at h
  exact hx (add_mem h.1 h.2)

namespace Proj

open HomogeneousLocalization CategoryTheory

noncomputable section ofGlobalSections

variable {X : Scheme.{u}} (f : A →+* Γ(X, ⊤))

/-- On the basic open `D(f t)`, the morphism `D(f t) ⟶ D₊(t) ≅ Spec (A_t)₀` induced by
`f : A →+* Γ(X, ⊤)` is `Spec` of the ring homomorphism `(A_t)₀ →+* Γ(X, D(f t))` sending
`a / tⁿ` to `f a / (f t)ⁿ`. -/
lemma toBasicOpenOfGlobalSections_eq {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      (X.basicOpen (f t)).toSpecΓ ≫
        Spec.map (CommRingCat.ofHom (Away.lift 𝒜
          ((algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (f t))).comp f)
          (Scheme.isUnit_algebraMap_basicOpen (f t)))) ≫
        (basicOpenIsoSpec 𝒜 t hd h0d).inv := by
  rw [toBasicOpenOfGlobalSections]
  simp only [← Category.assoc]
  rw [cancel_mono]
  simp only [Category.assoc, Scheme.isoOfEq_inv, ← Scheme.Hom.resLE_eq_morphismRestrict,
    Scheme.Hom.map_resLE, toSpecΓ_resLE_basicOpenIsoSpecAway_assoc]
  congr 1
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 1
  rw [Away.lift, ← RingHom.comp_assoc]
  congr 2
  refine IsLocalization.ringHom_ext (Submonoid.powers t) ?_
  rw [RingHom.comp_assoc, IsLocalization.map_comp, ← RingHom.comp_assoc,
    IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]

variable (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)

/-- If `t` is homogeneous of positive degree and `g : Y ⟶ X` is a morphism such that the
pullback of `f t` along `g` is a unit, then `g ≫ fromOfGlobalSections 𝒜 f hf` factors
through the affine chart `Spec (A_t)₀ ⟶ Proj 𝒜`, via the ring homomorphism sending
`a / tⁿ` to `Γ(g)(f a) / Γ(g)(f t)ⁿ`. -/
@[reassoc]
lemma comp_fromOfGlobalSections_eq_awayι {Y : Scheme.{u}} (g : Y ⟶ X) {t : A} {d : ℕ}
    (h0d : 0 < d) (hd : t ∈ 𝒜 d) (hu : IsUnit ((g.appTop.hom.comp f) t)) :
    g ≫ fromOfGlobalSections 𝒜 f hf =
      Y.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Away.lift 𝒜 (g.appTop.hom.comp f) hu)) ≫
        awayι 𝒜 t hd h0d := by
  have hle : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ X.basicOpen (f t) := by
    rw [Scheme.preimage_basicOpen_top]
    exact (Y.basicOpen_of_isUnit hu).ge
  have hE := congrArg (· ≫ (basicOpen 𝒜 t).ι) (fromOfGlobalSections_resLE 𝒜 f hf h0d hd)
  rw [toBasicOpenOfGlobalSections_eq] at hE
  simp only [Scheme.Hom.resLE_comp_ι, Category.assoc, basicOpenIsoSpec_inv_ι] at hE
  have happ0 : CommRingCat.ofHom (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (f t))) ≫
      Scheme.Hom.appLE g (X.basicOpen (f t)) ⊤ hle = g.appTop := by
    rw [show CommRingCat.ofHom (algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (f t))) =
        X.presheaf.map (homOfLE (X.basicOpen_le (f t))).op from rfl, Scheme.Hom.map_appLE]
    simp [Scheme.Hom.appLE]
  have happ : (Scheme.Hom.appLE g (X.basicOpen (f t)) ⊤ hle).hom.comp
      ((algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (f t))).comp f) = g.appTop.hom.comp f := by
    rw [← RingHom.comp_assoc]
    exact congrArg (RingHom.comp · f) (congrArg CommRingCat.Hom.hom happ0)
  have hcomp : CommRingCat.ofHom (Away.lift 𝒜
        ((algebraMap Γ(X, ⊤) Γ(X, X.basicOpen (f t))).comp f)
        (Scheme.isUnit_algebraMap_basicOpen (f t))) ≫
      Scheme.Hom.appLE g (X.basicOpen (f t)) ⊤ hle =
      CommRingCat.ofHom (Away.lift 𝒜 (g.appTop.hom.comp f) hu) := by
    rw [show Scheme.Hom.appLE g (X.basicOpen (f t)) ⊤ hle =
        CommRingCat.ofHom (Scheme.Hom.appLE g (X.basicOpen (f t)) ⊤ hle).hom from rfl,
      ← CommRingCat.ofHom_comp, Away.comp_lift]
    exact congrArg CommRingCat.ofHom
      (Away.lift_congr 𝒜 (ψ := g.appTop.hom.comp f) _ hu happ)
  rw [← cancel_epi Y.topIso.hom, Scheme.topIso_hom,
    ← Scheme.Hom.resLE_comp_ι_assoc g hle, hE,
    ← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, Scheme.Opens.toSpecΓ_top, Category.assoc,
    ← Spec.map_comp_assoc, hcomp]

/-- `Proj.fromOfGlobalSections` is natural in `X`: precomposing the morphism associated to
`f : A →+* Γ(X, ⊤)` with `g : Y ⟶ X` gives the morphism associated to `Γ(g) ∘ f`.

The hypothesis `hf'` follows from `hf` by `Ideal.map_map` and `Ideal.map_top`. -/
@[reassoc]
lemma comp_fromOfGlobalSections {Y : Scheme.{u}} (g : Y ⟶ X)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤) :
    g ≫ fromOfGlobalSections 𝒜 f hf = fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (g.appTop.hom.comp f) hf').hom_ext _ _ fun i ↦ ?_
  obtain ⟨n, r, hn, hr⟩ := i
  simp only [openCoverOfMapIrrelevantEqTop, Scheme.openCoverOfIsOpenCover_f]
  set V := Y.basicOpen ((g.appTop.hom.comp f) r)
  have hui : IsUnit ((V.ι.appTop.hom.comp (g.appTop.hom.comp f)) r) :=
    Scheme.Opens.isUnit_ι_appTop _ le_rfl
  have hu2 : IsUnit (((V.ι ≫ g).appTop.hom.comp f) r) := by
    simpa [Scheme.Hom.comp_appTop] using hui
  rw [← Category.assoc, comp_fromOfGlobalSections_eq_awayι 𝒜 f hf (V.ι ≫ g) hn hr hu2,
    comp_fromOfGlobalSections_eq_awayι 𝒜 _ hf' V.ι hn hr hui,
    Away.lift_congr 𝒜 (f := r) hu2 hui
      (by rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc])]

/-- `Proj.fromOfGlobalSections` only depends on `f` up to rescaling by a unit: if
`f' a = uᵈ * f a` for every `a` homogeneous of degree `d` and a fixed unit `u : Γ(X, ⊤)ˣ`,
then `f` and `f'` induce the same morphism `X ⟶ Proj 𝒜`. -/
lemma fromOfGlobalSections_eq_of_eq_unit_pow_mul (u : Γ(X, ⊤)ˣ) (f' : A →+* Γ(X, ⊤))
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f' = ⊤)
    (h : ∀ (d : ℕ) (a : A), a ∈ 𝒜 d → f' a = (u : Γ(X, ⊤)) ^ d * f a) :
    fromOfGlobalSections 𝒜 f' hf' = fromOfGlobalSections 𝒜 f hf := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun i ↦ ?_
  obtain ⟨n, r, hn, hr⟩ := i
  simp only [openCoverOfMapIrrelevantEqTop, Scheme.openCoverOfIsOpenCover_f]
  set V := X.basicOpen (f r)
  have hu1 : IsUnit ((V.ι.appTop.hom.comp f) r) := Scheme.Opens.isUnit_ι_appTop _ le_rfl
  have hu2 : IsUnit ((V.ι.appTop.hom.comp f') r) := by
    rw [RingHom.comp_apply, h n r hr, map_mul, map_pow]
    exact ((u.isUnit.map V.ι.appTop.hom).pow n).mul hu1
  rw [comp_fromOfGlobalSections_eq_awayι 𝒜 f' hf' V.ι hn hr hu2,
    comp_fromOfGlobalSections_eq_awayι 𝒜 f hf V.ι hn hr hu1,
    Away.lift_eq_lift_of_eq_unit_pow_mul 𝒜 (Units.map V.ι.appTop.hom.toMonoidHom u) hr
      (V.ι.appTop.hom.comp f) (V.ι.appTop.hom.comp f') hu1 hu2
      fun m a ha ↦ by simp [h m a ha]]

/-- If `f t` is a unit for some `t` homogeneous of positive degree, then
`Proj.fromOfGlobalSections` factors through the affine chart `Spec (A_t)₀ ⟶ Proj 𝒜`. -/
lemma fromOfGlobalSections_eq_toSpecΓ_awayι {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (hu : IsUnit (f t)) :
    fromOfGlobalSections 𝒜 f hf =
      X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Away.lift 𝒜 f hu)) ≫ awayι 𝒜 t hd h0d := by
  have hid : ((𝟙 X : X ⟶ X).appTop.hom.comp f) = f := by simp
  have hu' : IsUnit (((𝟙 X : X ⟶ X).appTop.hom.comp f) t) := by rw [hid]; exact hu
  have key := comp_fromOfGlobalSections_eq_awayι 𝒜 f hf (𝟙 X) h0d hd hu'
  rwa [Category.id_comp, Away.lift_congr 𝒜 (f := t) hu' hu hid] at key

/-- The affine chart formula: for `φ : A →+* R` and `t` homogeneous of positive degree with
`φ t` a unit, the morphism `Spec R ⟶ Proj 𝒜` associated to `φ` is `Spec` of the induced map
`HomogeneousLocalization.Away.lift 𝒜 φ hu : (A_t)₀ →+* R` followed by the chart inclusion
`Spec (A_t)₀ ⟶ Proj 𝒜`. -/
lemma fromOfGlobalSections_eq_awayι {R : CommRingCat.{u}} (φ : A →+* R)
    (hφ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map ((Scheme.ΓSpecIso R).inv.hom.comp φ) = ⊤)
    {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d) (hu : IsUnit (φ t)) :
    fromOfGlobalSections 𝒜 ((Scheme.ΓSpecIso R).inv.hom.comp φ) hφ =
      Spec.map (CommRingCat.ofHom (Away.lift 𝒜 φ hu)) ≫ awayι 𝒜 t hd h0d := by
  have hu' : IsUnit (((Scheme.ΓSpecIso R).inv.hom.comp φ) t) :=
    hu.map (Scheme.ΓSpecIso R).inv.hom
  rw [fromOfGlobalSections_eq_toSpecΓ_awayι 𝒜 _ hφ h0d hd hu',
    ← Away.comp_lift 𝒜 φ hu (Scheme.ΓSpecIso R).inv.hom, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_hom, Spec.map_comp]
  simp

end ofGlobalSections

end Proj

end AlgebraicGeometry
