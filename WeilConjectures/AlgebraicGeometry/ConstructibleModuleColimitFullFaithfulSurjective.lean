/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitHomData
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitPresentationData
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitFreeLift
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleColimitRelationFactor

/-! # Surjectivity half of constructible module Hom descent

Source: Stacks Project, Étale Cohomology, Lemma 09YU (3), fully faithful paragraph
(blueprint: lem-weil-pbc-constructible-module-colimit-full-faithful-surjective).

The proof uses the finite affine free presentation of the constructible source, the
finite-family eventual Hom lift, and the stabilization zero clause to kill the
relations before factoring through the cokernel.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
namespace AlgebraicGeometry

/-- Every morphism on the inverse-limit scheme is represented by a morphism at a later
stage, for a constructible finite-coefficient module source.

Proof: choose the finite affine free presentation `V → U → F₀ → 0`. Lift the
map from the pullback of `U` to the limit target to a later stage using the finite-family
free Hom-lift theorem. The composites with the finitely many summands of `V` pull back to
zero. The relation source is constructible, by comparison of its free summands with
extensions by zero of finite constant modules. The stabilization zero clause kills the
relation composite at a later stage. Exactness of inverse
image says the pulled-back presentation remains a cokernel, so the lifted map factors
uniquely through `F₀` at that stage. The inverse-image composition comparison identifies
its pullback with the original map. (blueprint:
lem-weil-pbc-constructible-module-colimit-full-faithful-surjective) -/
theorem constructibleModuleColimitCanonicalMap_surjective
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
    ∀ ψ : ((Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).obj F₀ ⟶
      (Etale.upperStar (ModuleCat.{u + 1} A) (c.π.app (op i₀))).obj G₀),
      ∃ i φ, ConstructibleModuleColimitCanonicalMap D c i₀ A F₀ G₀ i φ = ψ := by
  intro ψ
  let P : (D.obj (op i₀)).Etale →
      Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A) := fun W ↦
    (presheafToSheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} A)).obj
      (uliftYoneda.{u + 1}.obj W ⋙ ModuleCat.free A)
  obtain ⟨n, m, U, V, hU, hV, f, g, w, hc'⟩ :=
    Scheme.exists_affine_free_etale_presentation (D.obj (op i₀)) A F₀ hF₀
  let p : ConstructibleModuleFinitePresentationData A F₀ hF₀ :=
    { n := n, m := m, U := U, V := V, hU := hU, hV := hV, P := P,
      P_eq := rfl, f := f, g := g, w := w, hc := hc' }
  obtain ⟨i, h, a, ha⟩ :=
    constructibleModuleFinitePresentation_free_lift D c hc i₀ A F₀ G₀ hF₀ hG₀ p ψ
  obtain ⟨k, φ, hφ⟩ :=
    constructibleModuleFinitePresentation_relation_factor D c hc i₀ A F₀ G₀ hF₀ hG₀ p ψ
      i h a ha
  exact ⟨k, φ, hφ⟩

end AlgebraicGeometry
