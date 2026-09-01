/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Basic opens of `Proj`

We record `AlgebraicGeometry.Proj.basicOpen_add_le`, the analogue for `Proj.basicOpen`
of `AlgebraicGeometry.Scheme.basicOpen_add_le`: `D₊(f + g) ⊆ D₊(f) ∪ D₊(g)`.

We also identify the composite of `AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections` with
the isomorphism `D₊(t) ≅ Spec (A_t)₀` as a morphism of affine schemes, in
`AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom`.
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

open CategoryTheory HomogeneousLocalization

/-- The morphism `D(f t) ⟶ D₊(t)` attached to a map `f : A →+* Γ(X, ⊤)`, read through the
isomorphism `D₊(t) ≅ Spec (A_t)₀`, is the morphism of affine schemes given by the map
`(A_t)₀ → A_t → Γ(X, ⊤)_{f t}`. -/
lemma Proj.toBasicOpenOfGlobalSections_basicOpenIsoSpec_hom {X : Scheme.{u}}
    (f : A →+* Γ(X, ⊤)) {x : Γ(X, ⊤)} {t : A} {d : ℕ} (H : f t = x) (h0d : 0 < d)
    (hd : t ∈ 𝒜 d) :
    Proj.toBasicOpenOfGlobalSections 𝒜 f H h0d hd ≫ (Proj.basicOpenIsoSpec 𝒜 t hd h0d).hom =
      X.toSpecAway x ≫ Spec.map (CommRingCat.ofHom
        ((IsLocalization.map (M := .powers t) (T := .powers x) _ f (by
            rw [← Submonoid.map_le_iff_le_comap, Submonoid.map_powers]
            simp [H])).comp
          (algebraMap (Away 𝒜 t) (Localization.Away t)))) := by
  rw [Proj.toBasicOpenOfGlobalSections, Category.assoc, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, Scheme.toSpecAway, Category.assoc]
  rfl

end AlgebraicGeometry
