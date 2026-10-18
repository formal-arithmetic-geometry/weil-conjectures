-- Q62 stage-2 statement packet; declaration retained from the existing project module.
/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# Normalizing an orthogonal triangle to an adjunction counit

Source: Weil conjectures blueprint, main-20261015, six functors basics,
`sk-prop-closed-adjoint-constructible-support.proof.md`, first paragraph, counit
identification; Stacks Project, Tags 0149, 0037 and 0145
(blueprint: lem-sfb-orthogonal-triangle-counit-normalization).
-/

@[expose] public section

universe vC vT uC uT

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Normalize the first map of an orthogonal distinguished triangle to the counit of the
specified natural Hom bijections. Source: blueprint main-20261015,
`sk-prop-closed-adjoint-constructible-support.proof.md`, first paragraph; Stacks Tags
0149, 0037 and 0145 (blueprint: lem-sfb-orthogonal-triangle-counit-normalization).

Proof plan:
1. For every `A`, postcomposition with `a` from `Hom(F A, F G K)` to `Hom(F A, K)`
is bijective. Surjectivity follows from `Triangle.coyoneda_exact₂` and vanishing of
`Hom(F A, B)`. For injectivity, shift the difference of two lifts; its composite with
`a[1]` vanishes, so `Triangle.coyoneda_exact₁` factors it through `d`. The resulting
map `F A[1] → B` is zero: inverse shift identifies it with a map `F A → B[-1]`.
Faithfulness of shift then makes the original difference zero. This is the argument of
[lem-weil-pbc-hom-into-triangle-exact] using the additive invertible shift of
[def-weil-triangulated-category].
2. Compose this bijection with full faithfulness of `F` and the specified adjunction
bijection. Naturality in `A` identifies it with postcomposition by the transpose `u`.
The inverse-transpose formula also gives `a = F.map u ≫ counit.app K`; these are the
formulas of [lem-weil-pbc-adjunction-of-natural-bijection].
3. At `A = G K`, surjectivity gives `v ≫ u = 𝟙`. Then
`(u ≫ v) ≫ u = u = (𝟙 _) ≫ u`, so injectivity gives `u ≫ v = 𝟙`.
Thus `u` is invertible, and its image under `F` is invertible.
4. Set the new connecting map to `d ≫ (F.map u)[1]`. The counit factorization,
the unchanged second arrow, and this connecting-map formula are exactly the three
squares for the triangle morphism `(F.map u, 𝟙 K, 𝟙 B)`. Its componentwise inverse
uses `F.map v`; functoriality and the two inverse identities verify its squares.
These triples are inverse triangle morphisms. By TR1, the normalized triangle is
distinguished, since the original triangle is distinguished.
-/
theorem orthogonalTriangle_counit_normalization
    {C : Type uC} {T : Type uT} [Category.{vC} C] [Category.{vT} T]
    [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
    [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T]
    (F : C ⥤ T) [F.Full] [F.Faithful] (G : T ⥤ C)
    (Ψ : Adjunction.CoreHomEquiv F G) (K B : T)
    (a : F.obj (G.obj K) ⟶ K) (b : K ⟶ B)
    (d : B ⟶ (F.obj (G.obj K))⟦(1 : ℤ)⟧)
    (htriangle : Triangle.mk a b d ∈ distTriang T)
    (horthogonal : ∀ (A : C) (f : F.obj A ⟶ B), f = 0)
    (horthogonal_shift : ∀ (A : C) (f : F.obj A ⟶ B⟦(-1 : ℤ)⟧), f = 0)
    (u : G.obj K ⟶ G.obj K) (hu : u = Ψ.homEquiv (G.obj K) K a) :
    IsIso u ∧
      a = F.map u ≫ (Adjunction.mkOfHomEquiv Ψ).counit.app K ∧
      Triangle.mk ((Adjunction.mkOfHomEquiv Ψ).counit.app K) b
        (d ≫ (F.map u)⟦(1 : ℤ)⟧') ∈ distTriang T ∧
      ∃ e : Triangle.mk a b d ≅
          Triangle.mk ((Adjunction.mkOfHomEquiv Ψ).counit.app K) b
            (d ≫ (F.map u)⟦(1 : ℤ)⟧'),
        e.hom.hom₁ = F.map u ∧ e.hom.hom₂ = 𝟙 K ∧ e.hom.hom₃ = 𝟙 B := by
  sorry

end CategoryTheory
