/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Basic opens of `Proj` and the morphisms induced by global sections

We record `AlgebraicGeometry.Proj.basicOpen_add_le`, the analogue for `Proj.basicOpen`
of `AlgebraicGeometry.Scheme.basicOpen_add_le`: `D₊(f + g) ⊆ D₊(f) ∪ D₊(g)`.

We also record the two basic invariance properties of
`AlgebraicGeometry.Proj.fromOfGlobalSections`, the morphism `X ⟶ Proj 𝒜` induced by a ring
homomorphism `f : A →+* Γ(X, ⊤)` whose image of the irrelevant ideal generates the unit ideal:

- `AlgebraicGeometry.Proj.comp_fromOfGlobalSections`: naturality in `X`, i.e. precomposing
  with `g : Y ⟶ X` gives the morphism induced by `Γ(g) ∘ f`;
- `AlgebraicGeometry.Proj.fromOfGlobalSections_eq_of_unit_pow_mul`: rescaling `f` in degree
  `i` by the `i`-th power of a unit of `Γ(X, ⊤)` does not change the induced morphism.
-/

@[expose] public section

universe u

open HomogeneousLocalization CategoryTheory

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

variable {X Y : Scheme.{u}}

section fromOfGlobalSections

set_option backward.isDefEq.respectTransparency.types false in
/-- The description of `Proj.toBasicOpenOfGlobalSections` after identifying `D₊(t)` with
`Spec (A_t)₀`. -/
lemma toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom (f : A →+* Γ(X, ⊤))
    {t : A} {d : ℕ} {x : Γ(X, ⊤)} (H : f t = x) (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (hx : Submonoid.powers t ≤ (Submonoid.powers x).comap f) :
    toBasicOpenOfGlobalSections 𝒜 f H h0d hd ≫ (basicOpenIsoSpec 𝒜 t hd h0d).hom =
      X.toSpecΓ.resLE (PrimeSpectrum.basicOpen x) (X.basicOpen x)
          (X.toSpecΓ_preimage_basicOpen x).ge ≫
        (basicOpenIsoSpecAway x).hom ≫
          Spec.map (CommRingCat.ofHom
            ((IsLocalization.map (S := Localization.Away t) (Localization.Away x) f hx).comp
              (algebraMap (Away 𝒜 t) (Localization.Away t)))) := by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict, Category.assoc, Scheme.Hom.map_resLE_assoc,
    Iso.inv_hom_id, Category.comp_id]

/-- The morphism `X ⟶ Proj 𝒜` induced by `f : A →+* Γ(X, ⊤)` restricted to `D(f r)`
is `Proj.toBasicOpenOfGlobalSections`. -/
@[reassoc]
lemma ι_comp_fromOfGlobalSections (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {r : A} {n : ℕ} (hn : 0 < n)
    (hr : r ∈ 𝒜 n) :
    (X.basicOpen (f r)).ι ≫ fromOfGlobalSections 𝒜 f hf =
      toBasicOpenOfGlobalSections 𝒜 f rfl hn hr ≫ (basicOpen 𝒜 r).ι := by
  rw [← Scheme.Hom.resLE_comp_ι (fromOfGlobalSections 𝒜 f hf)
    (fromOfGlobalSections_preimage_basicOpen 𝒜 f hf hn hr).ge,
    fromOfGlobalSections_resLE]

section naturality

variable (g : Y ⟶ X) (f : A →+* Γ(X, ⊤))

/-- If the image of the irrelevant ideal under `f : A →+* Γ(X, ⊤)` generates the unit ideal,
the same holds after composing with the restriction along a morphism of schemes. -/
lemma map_irrelevant_comp_appTop_eq_top
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤ := by
  rw [← Ideal.map_map, hf, Ideal.map_top]

/-- The basic open of `Γ(g) (f r)` in `Y` is contained in (in fact equal to) the preimage of
the basic open of `f r` in `X`. -/
lemma basicOpen_comp_appTop_le_preimage (r : A) :
    Y.basicOpen ((g.appTop.hom.comp f) r) ≤ g ⁻¹ᵁ X.basicOpen (f r) :=
  (Scheme.preimage_basicOpen_top g (f r)).ge

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of `Proj.toBasicOpenOfGlobalSections` in the source scheme, after identifying
`D₊(t)` with `Spec (A_t)₀`. -/
@[reassoc]
private lemma resLE_toSpecΓ_comp_SpecMap_map (t : A) :
    g.resLE (X.basicOpen (f t)) (Y.basicOpen ((g.appTop.hom.comp f) t))
        (basicOpen_comp_appTop_le_preimage g f t) ≫
      (X.toSpecΓ.resLE (PrimeSpectrum.basicOpen (f t)) (X.basicOpen (f t))
          (X.toSpecΓ_preimage_basicOpen (f t)).ge ≫
        (basicOpenIsoSpecAway (f t)).hom ≫
          Spec.map (CommRingCat.ofHom
            (IsLocalization.map (S := Localization.Away t) (T := Submonoid.powers (f t))
              (Localization.Away (f t)) f
              (Submonoid.powers_le.mpr (Submonoid.mem_powers _))))) =
      Y.toSpecΓ.resLE (PrimeSpectrum.basicOpen ((g.appTop.hom.comp f) t))
          (Y.basicOpen ((g.appTop.hom.comp f) t))
          (Y.toSpecΓ_preimage_basicOpen _).ge ≫
        (basicOpenIsoSpecAway ((g.appTop.hom.comp f) t)).hom ≫
          Spec.map (CommRingCat.ofHom (IsLocalization.map (S := Localization.Away t)
            (T := Submonoid.powers ((g.appTop.hom.comp f) t))
            (Localization.Away ((g.appTop.hom.comp f) t)) (g.appTop.hom.comp f)
            (Submonoid.powers_le.mpr (Submonoid.mem_powers _)))) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))))]
  have e1 : ∀ {R : Type u} [CommRing R] (φ : A →+* R) (r : R)
      (h : Submonoid.powers t ≤ (Submonoid.powers r).comap φ),
      Spec.map (CommRingCat.ofHom
          (IsLocalization.map (S := Localization.Away t) (Localization.Away r) φ h)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away t))) =
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) ≫
        Spec.map (CommRingCat.ofHom φ) := by
    intro R _ φ r h
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact IsLocalization.map_comp _
  simp only [Category.assoc, e1, resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap_assoc,
    Scheme.Hom.resLE_comp_ι_assoc, CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom,
    ← Scheme.toSpecΓ_naturality_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- Naturality of `Proj.toBasicOpenOfGlobalSections` in the source scheme. -/
@[reassoc]
lemma resLE_toBasicOpenOfGlobalSections {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    g.resLE (X.basicOpen (f t)) (Y.basicOpen ((g.appTop.hom.comp f) t))
        (basicOpen_comp_appTop_le_preimage g f t) ≫
      toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) rfl h0d hd := by
  rw [← cancel_mono (basicOpenIsoSpec 𝒜 t hd h0d).hom, Category.assoc,
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 f rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 (g.appTop.hom.comp f) rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_comp, Spec.map_comp,
    resLE_toSpecΓ_comp_SpecMap_map_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- The morphism `X ⟶ Proj 𝒜` induced by a ring homomorphism `f : A →+* Γ(X, ⊤)` is natural
in `X`: precomposing with `g : Y ⟶ X` gives the morphism induced by `Γ(g) ∘ f`. -/
@[reassoc]
lemma comp_fromOfGlobalSections
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤) :
    g ≫ fromOfGlobalSections 𝒜 f hf =
      fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (g.appTop.hom.comp f) hf').hom_ext _ _ fun i ↦ ?_
  obtain ⟨n, r, hn, hr⟩ := i
  have key : (Y.basicOpen ((g.appTop.hom.comp f) r)).ι ≫ g ≫ fromOfGlobalSections 𝒜 f hf =
      toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) rfl hn hr ≫ (basicOpen 𝒜 r).ι := by
    rw [← Category.assoc,
      ← Scheme.Hom.resLE_comp_ι g (basicOpen_comp_appTop_le_preimage g f r),
      Category.assoc, ι_comp_fromOfGlobalSections 𝒜 f hf hn hr,
      resLE_toBasicOpenOfGlobalSections_assoc]
  exact key.trans (ι_comp_fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' hn hr).symm

end naturality

section unitPowMul

set_option backward.isDefEq.respectTransparency.types false in
/-- Rescaling `f` in degree `i` by the `i`-th power of a unit does not change
`Proj.toBasicOpenOfGlobalSections`. -/
lemma toBasicOpenOfGlobalSections_eq_of_unit_pow_mul (u : Γ(X, ⊤)ˣ) (f f' : A →+* Γ(X, ⊤))
    (hff' : ∀ (i : ℕ) (a : A), a ∈ 𝒜 i → f' a = (u : Γ(X, ⊤)) ^ i * f a)
    {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (hbo : X.basicOpen (f t) = X.basicOpen (f' t)) :
    toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      X.homOfLE hbo.le ≫ toBasicOpenOfGlobalSections 𝒜 f' rfl h0d hd := by
  have hft : f' t = (u : Γ(X, ⊤)) ^ d * f t := hff' d t hd
  have hunit : ∀ y : Submonoid.powers (f' t),
      IsUnit (algebraMap Γ(X, ⊤) (Localization.Away (f t)) (y : Γ(X, ⊤))) := by
    rintro ⟨y, k, rfl⟩
    change IsUnit (algebraMap Γ(X, ⊤) (Localization.Away (f t)) (f' t ^ k))
    rw [hft, mul_pow, map_mul]
    exact (((u.isUnit.pow d).pow k).map _).mul
      (IsLocalization.map_units _ (⟨f t ^ k, k, rfl⟩ : Submonoid.powers (f t)))
  set ε : Localization.Away (f' t) →+* Localization.Away (f t) :=
    IsLocalization.lift (M := Submonoid.powers (f' t)) hunit with hε
  have ha : X.homOfLE hbo.le ≫ X.toSpecΓ.resLE (PrimeSpectrum.basicOpen (f' t))
        (X.basicOpen (f' t)) (X.toSpecΓ_preimage_basicOpen (f' t)).ge ≫
        (basicOpenIsoSpecAway (f' t)).hom =
      X.toSpecΓ.resLE (PrimeSpectrum.basicOpen (f t)) (X.basicOpen (f t))
          (X.toSpecΓ_preimage_basicOpen (f t)).ge ≫
        (basicOpenIsoSpecAway (f t)).hom ≫ Spec.map (CommRingCat.ofHom ε) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom
      (algebraMap Γ(X, ⊤) (Localization.Away (f' t)))))]
    simp only [Category.assoc]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hε, IsLocalization.lift_comp,
      resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap,
      resLE_toSpecΓ_basicOpenIsoSpecAway_hom_SpecMap, Scheme.homOfLE_ι_assoc]
  have hb : ε.comp ((IsLocalization.map (S := Localization.Away t)
        (T := Submonoid.powers (f' t)) (Localization.Away (f' t)) f'
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _))).comp
        (algebraMap (Away 𝒜 t) (Localization.Away t))) =
      (IsLocalization.map (S := Localization.Away t) (T := Submonoid.powers (f t))
        (Localization.Away (f t)) f
        (Submonoid.powers_le.mpr (Submonoid.mem_powers _))).comp
        (algebraMap (Away 𝒜 t) (Localization.Away t)) := by
    ext z
    obtain ⟨k, a, hak, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hd z
    have hval : algebraMap (Away 𝒜 t) (Localization.Away t)
        (HomogeneousLocalization.Away.mk 𝒜 hd k a hak) =
        IsLocalization.mk' (Localization.Away t) a
          (⟨t ^ k, k, rfl⟩ : Submonoid.powers t) := by
      rw [HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
        Localization.mk_eq_mk']
    simp only [RingHom.coe_comp, Function.comp_apply, hval, IsLocalization.map_mk', hε,
      IsLocalization.lift_mk'_spec]
    rw [hff' _ _ hak, hff' _ _ (SetLike.pow_mem_graded k hd), map_mul, map_mul, mul_assoc,
      IsLocalization.mk'_spec'_mk]
  rw [← cancel_mono (basicOpenIsoSpec 𝒜 t hd h0d).hom, Category.assoc,
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 f rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    toBasicOpenOfGlobalSections_comp_basicOpenIsoSpec_hom 𝒜 f' rfl h0d hd
      (Submonoid.powers_le.mpr (Submonoid.mem_powers _)),
    reassoc_of% ha, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hb]

/-- Rescaling `f` in degree `i` by the `i`-th power of a unit of `Γ(X, ⊤)` does not change the
induced morphism `X ⟶ Proj 𝒜`. -/
lemma fromOfGlobalSections_eq_of_unit_pow_mul (u : Γ(X, ⊤)ˣ) (f f' : A →+* Γ(X, ⊤))
    (hff' : ∀ (i : ℕ) (a : A), a ∈ 𝒜 i → f' a = (u : Γ(X, ⊤)) ^ i * f a)
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f' = ⊤) :
    fromOfGlobalSections 𝒜 f hf = fromOfGlobalSections 𝒜 f' hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 f hf).hom_ext _ _ fun i ↦ ?_
  obtain ⟨n, r, hn, hr⟩ := i
  have hbo : X.basicOpen (f r) = X.basicOpen (f' r) := by
    rw [hff' n r hr, Scheme.basicOpen_mul,
      Scheme.basicOpen_of_isUnit _ ((u.isUnit.pow n : IsUnit ((u : Γ(X, ⊤)) ^ n))), top_inf_eq]
  simp only [openCoverOfMapIrrelevantEqTop, Scheme.openCoverOfIsOpenCover_f]
  rw [ι_comp_fromOfGlobalSections 𝒜 f hf hn hr,
    toBasicOpenOfGlobalSections_eq_of_unit_pow_mul 𝒜 u f f' hff' hn hr hbo, Category.assoc,
    ← ι_comp_fromOfGlobalSections 𝒜 f' hf' hn hr, Scheme.homOfLE_ι_assoc]

end unitPowMul

end fromOfGlobalSections

end Proj

end AlgebraicGeometry
