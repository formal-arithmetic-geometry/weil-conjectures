/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitHomData
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitStabilizationPairwise
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitStabilizationZero
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitStabilizationFinite

/-! # Stabilization half of constructible module Hom descent

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), faithful and fully faithful
paragraphs (blueprint: lem-weil-pbc-constructible-module-colimit-full-faithful-stabilization).

The proof uses a finite affine free presentation and section continuity. It applies the
filtered elementwise equality criterion after moving finitely many representatives to a
common stage, and therefore proves eventual equality, eventual vanishing, and the finite
family relation clause.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

/-- Equal limit morphisms between stages agree later, and zero and finite relation
families are detected at a common later stage.

Proof: use a finite affine free presentation of the constructible source and the
free-Yoneda evaluation bijection to reduce equality of maps to equality of finitely many
sections on affine etale generators. The elementwise filtered-colimit equality criterion,
together with section continuity, gives a common upper stage where all generator values
agree. The zero clause is the special case comparing with the zero map. For a finite
relation family, choose one common upper stage for all representatives and apply the
pairwise argument to the finitely many asserted relations; directedness supplies a single
upper bound. (blueprint:
lem-weil-pbc-constructible-module-colimit-full-faithful-stabilization) -/
theorem constructibleModuleColimitCanonicalMap_stabilizes
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
    (∀ (i j : ConstructibleModuleColimitAbove I i₀)
        (φ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ i)
        (ψ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ j),
      ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ i φ =
        ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ j ψ →
      ∃ (k : ConstructibleModuleColimitAbove I i₀) (f : i ⟶ k) (g : j ⟶ k),
        ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ f φ =
          ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ g ψ) ∧
    (∀ (i : ConstructibleModuleColimitAbove I i₀)
        (φ : ConstructibleModuleColimitHomType D i₀ A F₀ G₀ i),
      ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ i φ = 0 →
      ∃ (j : ConstructibleModuleColimitAbove I i₀) (f : i ⟶ j),
        ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ f φ = 0) ∧
    (∀ (n : ℕ) (i : Fin n → ConstructibleModuleColimitAbove I i₀)
        (φ : ∀ a, ConstructibleModuleColimitHomType D i₀ A F₀ G₀ (i a))
        (R : Fin n → Fin n → Prop),
      (∀ a b, R a b →
        ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ (i a) (φ a) =
          ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ (i b) (φ b)) →
      ∃ (k : ConstructibleModuleColimitAbove I i₀) (f : ∀ a, i a ⟶ k),
        ∀ a b, R a b →
          ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ (f a) (φ a) =
            ConstructibleModuleColimitHomMap D i₀ A F₀ G₀ (f b) (φ b)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact constructibleModuleColimitCanonicalMap_eventually_equal D c hc i₀ A F₀ G₀ hF₀ hG₀
  · exact constructibleModuleColimitCanonicalMap_eventually_zero D c hc i₀ A F₀ G₀ hF₀ hG₀
  · exact constructibleModuleColimitCanonicalMap_eventually_equal_finite D c hc i₀ A F₀ G₀ hF₀ hG₀

end AlgebraicGeometry
