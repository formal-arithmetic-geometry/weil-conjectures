/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Scalar extension of affine Proj with its chart maps

Source: literature/stacks-project/constructions.tex, Tags 01N2 and 01MY
(blueprint: lem-nagata-affine-proj-scalar-extension)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Scalar extension of affine Proj, with the standard-open descriptions.
Source: Stacks Project, Tags 01N2 and 01MY (blueprint: lem-nagata-affine-proj-scalar-extension).
Proof: the graded scalar-extension condition expresses every positive-degree element of B
as a finite S-linear combination of images of homogeneous elements of A. These images generate
the irrelevant ideal, so their standard opens cover (def-nagata-affine-proj). On each such open,
lem-nagata-homogeneous-localization-scalar-extension and
lem-weil-pbc-fibre-product-affine-spectra identify the chart with the affine fibre product.
The projection is induced by Away.map, whose fraction formula is Away.map_mk.
On intersections, lem-weil-pbc-proj-basic-open-intersection and
lemma-nagata-proj-chart-ring-cocycle identify both projections with the same fraction map.
Then lem-weil-pbc-scheme-morphism-gluing glues them and proves the inverse-image formula.
For any test scheme with compatible maps to Proj A and Spec S, restrict to these opens,
use chartwise pullback uniqueness, and glue the lifts; this proves the cartesian square
(def-pc-fibre-product). Finally, maps with the stated chart formulas agree on the cover,
so gluing uniqueness proves the final clause. No cancellation or flatness is used.
-/
theorem lem_nagata_affine_proj_scalar_extension
    {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    {A : Type u} [CommRing A] {B : Type u} [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (ρA : R →+* 𝒜 0) (ρB : S →+* ℬ 0)
    (hρA : ∀ r : R, (ρA r : A) = algebraMap R A r)
    (hρB : ∀ s : S, (ρB s : B) = algebraMap S B s)
    (β : TensorProduct R S A ≃ₐ[S] B)
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A))) :
    ∃ (r : Proj ℬ ⟶ Proj 𝒜),
      CategoryTheory.IsPullback r
        (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom ρB))
        (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom ρA))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ∧
      (∀ (n : ℕ) (f : A), f ∈ 𝒜 n → 0 < n →
        r ⁻¹ᵁ Proj.basicOpen 𝒜 f = Proj.basicOpen ℬ (ψ f)) ∧
      (∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
        Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hn ≫ r =
          Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
            Proj.awayι 𝒜 f hf hn) ∧
      (⨆ (p : {p : ℕ × A // p.2 ∈ 𝒜 p.1 ∧ 0 < p.1}),
        Proj.basicOpen ℬ (ψ p.1.2)) = ⊤ ∧
      (∀ r' : Proj ℬ ⟶ Proj 𝒜,
        (∀ (n : ℕ) (f : A), f ∈ 𝒜 n → 0 < n →
          r' ⁻¹ᵁ Proj.basicOpen 𝒜 f = Proj.basicOpen ℬ (ψ f)) →
        (∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
          Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hn ≫ r' =
            Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
              Proj.awayι 𝒜 f hf hn) → r' = r) := by
  sorry

end AlgebraicGeometry
