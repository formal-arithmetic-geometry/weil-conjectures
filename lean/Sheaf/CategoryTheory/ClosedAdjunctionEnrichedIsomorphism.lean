/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group ND
-/
module

public import Sheaf.CategoryTheory.ClosedAdjunctionComparison

/-! # The evaluation-defined enriched adjunction isomorphism

Source: Stacks Project, Categories, Tag 0037 (definition-adjoint), adjunction-map formulas;
agent-written closed-bifunctor argument for the first and last mapping-complex comparisons
in prop-coef-integral-exceptional-adjoint, proof paragraph 2
(blueprint: lem-coef-closed-adjunction-enriched-isomorphism).
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

open CategoryTheory Opposite

namespace CategoryTheory.ClosedAdjunctionComparison

/-- The specified evaluation-defined adjunct is invertible and natural in both inputs.
Source: Stacks Project, Categories, Tag 0037 (definition-adjoint), adjunction-map formulas;
agent-written argument for prop-coef-integral-exceptional-adjoint, proof paragraph 2
(blueprint: lem-coef-closed-adjunction-enriched-isomorphism).

Here `evaluation` is the inverse closed transpose of the identity, `comparison` is the
closed transpose of mu followed by F(evaluation) followed by the counit, and
`adjointComparison` is the unit followed by G(comparison). These are the existing
constructions of lem-coef-closed-adjunction-naturality, with no new choices.

Proof plan:
1. Naturality of theta in its test object identifies inverse transposition of t with
   tensor(t, identity) followed by evaluation. This uses def-nagata-category's laws.
2. For fixed P,N, compose inverse thetaC, inverse adjunction Hom equivalence,
   precomposition by mu, thetaD, and the adjunction Hom equivalence. These are five
   bijections from Hom(T,HC(P,GN)) to Hom(T,G(HD(FP,N))). The normalized inverse
   adjunction sends h to F(h) followed by the counit, as in
   lem-weil-pbc-adjunction-of-natural-bijection.
3. Naturality of mu at (t,identity), then test-object naturality of thetaD, identifies
   this composite with t followed by adjointComparison. The adjunction's source
   naturality and its unit formula identify the final step with the specified adjunct.
4. Surjectivity at W = G(HD(FP,N)) gives s : W -> HC(P,GN) with s followed by delta
   equal to identity. Injectivity at HC(P,GN), and category associativity, show that
   delta followed by s is also identity. Thus the actual delta is invertible.
5. Apply lem-coef-closed-adjunction-naturality to the identical bifunctors, thetaC,
   thetaD, mu, and adjunction. Its second equality is precisely the naturality square
   asserted here. Componentwise invertibility makes these squares a natural isomorphism.
Only the tensor bifunctors and the stated naturalities enter the argument. -/
theorem enriched_isomorphism
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (tensorC : C × C ⥤ C) (tensorD : D × D ⥤ D)
    (HC : Cᵒᵖ × C ⥤ C) (HD : Dᵒᵖ × D ⥤ D)
    (θC : ∀ T X Y : C, (tensorC.obj (T, X) ⟶ Y) ≃ (T ⟶ HC.obj (op X, Y)))
    (θD : ∀ T X Y : D, (tensorD.obj (T, X) ⟶ Y) ≃ (T ⟶ HD.obj (op X, Y)))
    (F : C ⥤ D) (G : D ⥤ C)
    (μ : ∀ X Y : C, tensorD.obj (F.obj X, F.obj Y) ≅ F.obj (tensorC.obj (X, Y)))
    (adj : F ⊣ G)
    (hθC : ∀ (T T' X X' Y Y' : C) (k : tensorC.obj (T, X) ⟶ Y)
      (t : T' ⟶ T) (a : X' ⟶ X) (g : Y ⟶ Y'),
      θC T' X' Y' (tensorC.map (Prod.mkHom t a) ≫ k ≫ g) =
        t ≫ θC T X Y k ≫ HC.map (Prod.mkHom a.op g))
    (hθD : ∀ (T T' X X' Y Y' : D) (k : tensorD.obj (T, X) ⟶ Y)
      (t : T' ⟶ T) (a : X' ⟶ X) (g : Y ⟶ Y'),
      θD T' X' Y' (tensorD.map (Prod.mkHom t a) ≫ k ≫ g) =
        t ≫ θD T X Y k ≫ HD.map (Prod.mkHom a.op g))
    (hμ : ∀ (X X' Y Y' : C) (f : X ⟶ X') (g : Y ⟶ Y'),
      (μ X Y).hom ≫ F.map (tensorC.map (Prod.mkHom f g)) =
        tensorD.map (Prod.mkHom (F.map f) (F.map g)) ≫ (μ X' Y').hom)
    : (∀ (P : C) (N : D),
        IsIso (adjointComparison tensorC tensorD HC HD θC θD F G μ adj P N)) ∧
      (∀ (P P' : C) (N N' : D) (a : P' ⟶ P) (v : N ⟶ N'),
        HC.map (Prod.mkHom a.op (G.map v)) ≫
            adjointComparison tensorC tensorD HC HD θC θD F G μ adj P' N' =
          adjointComparison tensorC tensorD HC HD θC θD F G μ adj P N ≫
            G.map (HD.map (Prod.mkHom (F.map a).op v))) := by
  sorry

end CategoryTheory.ClosedAdjunctionComparison
