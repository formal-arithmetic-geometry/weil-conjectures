/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitHomData
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitStabilizationPairwise

/-! Eventual vanishing for constructible module Hom comparison.

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful paragraph
(blueprint: lem-weil-pbc-constructible-module-colimit-stabilization-zero).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

/-- A representative whose canonical pullback is zero vanishes at a later stage.

The proof is the zero specialization of the finite affine presentation and section
continuity argument, followed by the filtered-colimit zero criterion.
(blueprint: lem-weil-pbc-constructible-module-colimit-stabilization-zero) -/
theorem constructibleModuleColimitCanonicalMap_eventually_zero
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
    ∀ (i : ConstructibleModuleColimitAbove I i₀)
      (φ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ i),
      ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ i φ = 0 →
      ∃ (j : ConstructibleModuleColimitAbove I i₀) (f : i ⟶ j),
        ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ f φ = 0 := by
  intro i φ hφ
  let j : ConstructibleModuleColimitAbove I i₀ := i
  let ψ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ j := 0
  have hz : ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ j ψ = 0 := by
    dsimp [ConstructibleModuleColimitCanonicalMap, ψ]
    simp
  obtain ⟨k, f, g, h⟩ := constructibleModuleColimitCanonicalMap_eventually_equal
    D c hc i₀ A F₀ G₀ hF₀ hG₀ i j φ ψ (hφ.trans hz.symm)
  refine ⟨k, f, ?_⟩
  simpa [ConstructibleModuleColimitHomMap, ψ] using h

end AlgebraicGeometry
