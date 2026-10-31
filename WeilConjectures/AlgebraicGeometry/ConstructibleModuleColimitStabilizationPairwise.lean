/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitHomData

/-! Pairwise eventual equality for constructible module Hom comparison.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful paragraph
(blueprint: lem-weil-pbc-constructible-module-colimit-stabilization-pairwise).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

/-- Equality of two canonical Hom representatives is detected at one later stage.

The proof uses a finite affine free presentation of the source, free Yoneda evaluation,
section continuity on affine etale generators, and the elementwise equality criterion for
filtered colimits. These ingredients are independent of the finite-family argument.
(blueprint: lem-weil-pbc-constructible-module-colimit-stabilization-pairwise) -/
theorem constructibleModuleColimitCanonicalMap_eventually_equal
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)]
    [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : Iᵒᵖ} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (F₀ G₀ : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A))
    (hF₀ : Scheme.IsConstructibleEtaleModuleSheaf F₀)
    (hG₀ : Scheme.IsConstructibleEtaleModuleSheaf G₀) :
    ∀ (i j : ConstructibleModuleColimitAbove I i₀)
      (φ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ i)
      (ψ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ j),
      ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ i φ =
        ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ j ψ →
      ∃ (k : ConstructibleModuleColimitAbove I i₀) (f : i ⟶ k) (g : j ⟶ k),
        ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ f φ =
          ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ g ψ := by
  sorry

end AlgebraicGeometry
