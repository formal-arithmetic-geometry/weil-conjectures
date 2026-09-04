/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# Complements on schemes

* `AlgebraicGeometry.Scheme.isUnit_of_le_basicOpen`: if `U ≤ X.basicOpen f` for a section
  `f : Γ(X, U)`, then `f` is a unit. This is the converse of `Scheme.basicOpen_of_isUnit`.
* `AlgebraicGeometry.Scheme.Hom.appLE_top_top`: `appLE` between the top opens is `appTop`,
  the special case `U = V = ⊤` of `AlgebraicGeometry.Scheme.Hom.app_eq_appLE`.
* `AlgebraicGeometry.Scheme.specMap_appTop_ΓSpecIso_inv` and
  `AlgebraicGeometry.Scheme.specMap_appTop_ΓSpecIso_inv_mul_eq`: `Spec` of a ring map acts
  on global sections by the ring map, and transports a multiplicative relation.
* `AlgebraicGeometry.Scheme.zeroLocus_ΓSpecIso_inv_image`: on an affine scheme, the
  scheme-theoretic zero locus of a set of global sections is the prime-spectrum zero locus.
* `AlgebraicGeometry.Scheme.isClosed_range_comp_of_isIso`: composing with an isomorphism
  preserves closedness of the range.
* `AlgebraicGeometry.Scheme.exists_mem_basicOpen_of_span_eq_top`: if the numerators and
  denominators of a family of fractions generate the unit ideal and all the fraction
  equations vanish at a point, some denominator is invertible there.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A section of a scheme that is invertible at every point of its domain is a unit.
This is the converse of `Scheme.basicOpen_of_isUnit`. -/
theorem isUnit_of_le_basicOpen {X : Scheme.{u}} {U : X.Opens} {f : Γ(X, U)}
    (h : U ≤ X.basicOpen f) : IsUnit f :=
  X.toRingedSpace.isUnit_of_isUnit_germ U f fun x hx ↦ (X.mem_basicOpen f x hx).mp (h hx)

/-- The `appLE` of a morphism between the top opens is its `appTop`. This is
`Scheme.Hom.app_eq_appLE` specialised to `U = V = ⊤`. -/
@[simp]
lemma Hom.appLE_top_top {T T' : Scheme.{u}} (q : T ⟶ T')
    (h : (⊤ : T.Opens) ≤ q ⁻¹ᵁ ⊤) : q.appLE ⊤ ⊤ h = q.appTop := by
  simp [Scheme.Hom.appLE]

/-- `Spec` of a ring map acts on global sections by the ring map. -/
lemma specMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (φ : R ⟶ S) (r : R) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv r) = (Scheme.ΓSpecIso S).inv (φ r) := by
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]

/-- Composing with an isomorphism preserves closedness of the range. -/
lemma isClosed_range_comp_of_isIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Z) [IsIso e]
    (h : IsClosed (Set.range f.base)) : IsClosed (Set.range (f ≫ e).base) := by
  have hrange : Set.range (f ≫ e).base = e.base '' Set.range f.base := by
    rw [← Set.range_comp]
    rfl
  rw [hrange]
  exact (Scheme.Hom.homeomorph e).isClosedMap _ h

/-- A multiplicative relation between ring elements transported through `Spec` of two ring
maps into a common target. Stated for abstract rings so that the rewrites happen on small
terms; this is what makes it usable on the (very large) blow-up chart rings. -/
lemma specMap_appTop_ΓSpecIso_inv_mul_eq {R S T : CommRingCat.{u}} (φ : R ⟶ T) (ψ : S ⟶ T)
    (x : R) (y z : S) (h : φ x * ψ y = ψ z) :
    (Spec.map φ).appTop ((Scheme.ΓSpecIso R).inv x) *
        (Spec.map ψ).appTop ((Scheme.ΓSpecIso S).inv y) =
      (Spec.map ψ).appTop ((Scheme.ΓSpecIso S).inv z) := by
  rw [specMap_appTop_ΓSpecIso_inv, specMap_appTop_ΓSpecIso_inv,
    specMap_appTop_ΓSpecIso_inv, ← map_mul, h]

/-- The scheme-theoretic zero locus of the `ΓSpecIso`-preimage of a set of ring
elements is the prime-spectrum zero locus. -/
lemma zeroLocus_ΓSpecIso_inv_image {R : CommRingCat.{u}} (s : Set R) :
    (Spec R).zeroLocus (U := ⊤) ((Scheme.ΓSpecIso R).inv '' s) =
      PrimeSpectrum.zeroLocus s := by
  ext x
  rw [Scheme.mem_zeroLocus_iff, PrimeSpectrum.mem_zeroLocus]
  constructor
  · intro h e he
    have h2 := h _ (Set.mem_image_of_mem _ he)
    rw [basicOpen_eq_of_affine] at h2
    by_contra hne
    exact h2 ((PrimeSpectrum.mem_basicOpen _ _).mpr hne)
  · rintro h - ⟨e, he, rfl⟩
    rw [basicOpen_eq_of_affine]
    intro hmem
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hmem (h he)

/-- **Some element of a spanning family is invertible at a point.** Let `ψ : S ⟶ Γ(T, ⊤)`
be a ring map, `t : σ → Γ(T, ⊤)` a family of sections, and let `v i`, `w i j` be elements of
`S` generating the unit ideal. If none of the sections `ψ (v i) · t j − ψ (w i j)` is
invertible at a point `x` of `T`, then some `ψ (v i)` is: otherwise the images in the stalk
at `x` of all the `v i` and all the `w i j` would lie in the maximal ideal, which cannot
contain `1`. -/
lemma exists_mem_basicOpen_of_span_eq_top {T : Scheme.{u}} {S : CommRingCat.{u}}
    (ψ : S ⟶ Γ(T, ⊤)) {ι σ : Type*} (v : ι → S) (w : ι → σ → S) (t : σ → Γ(T, ⊤))
    (hone : (1 : S) ∈ Ideal.span (Set.range v ∪ ⋃ i, Set.range (w i)))
    {x : T} (hx : ∀ i j, x ∉ T.basicOpen (ψ (v i) * t j - ψ (w i j))) :
    ∃ i, x ∈ T.basicOpen (ψ (v i)) := by
  by_contra hnone
  push Not at hnone
  set φ := T.presheaf.germ ⊤ x trivial with hφ
  have hgermv : ∀ i, φ (ψ (v i)) ∈ IsLocalRing.maximalIdeal _ := by
    intro i
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    exact hnone i ((Scheme.mem_basicOpen_top _ _ x).mpr hunit)
  have hgermE : ∀ i j, φ (ψ (v i) * t j - ψ (w i j)) ∈ IsLocalRing.maximalIdeal _ := by
    intro i j
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    exact hx i j ((Scheme.mem_basicOpen_top _ _ x).mpr hunit)
  have hgermw : ∀ i j, φ (ψ (w i j)) ∈ IsLocalRing.maximalIdeal _ := by
    intro i j
    have hwe : ψ (w i j) = ψ (v i) * t j - (ψ (v i) * t j - ψ (w i j)) := by ring
    rw [hwe, map_sub, map_mul]
    exact sub_mem (Ideal.mul_mem_right _ _ (hgermv i)) (hgermE i j)
  have hmap : (1 : T.presheaf.stalk x) ∈
      Ideal.map (ψ ≫ φ).hom (Ideal.span (Set.range v ∪ ⋃ i, Set.range (w i))) := by
    simpa using Ideal.mem_map_of_mem (ψ ≫ φ).hom hone
  rw [Ideal.map_span] at hmap
  have hle : Ideal.span (⇑(ψ ≫ φ).hom '' (Set.range v ∪ ⋃ i, Set.range (w i))) ≤
      IsLocalRing.maximalIdeal _ := by
    rw [Ideal.span_le]
    rintro - ⟨e, he, rfl⟩
    rcases he with ⟨i, rfl⟩ | he
    · exact CommRingCat.comp_apply .. ▸ hgermv i
    · simp only [Set.mem_iUnion, Set.mem_range] at he
      obtain ⟨i, j, rfl⟩ := he
      exact CommRingCat.comp_apply .. ▸ hgermw i j
  exact absurd (hle hmap)
    ((Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal _).ne_top)

end AlgebraicGeometry.Scheme
