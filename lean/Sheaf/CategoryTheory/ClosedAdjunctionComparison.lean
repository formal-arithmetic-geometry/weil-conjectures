/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Naturality of the evaluation-defined closed adjunction comparison

Source: Stacks Project, Categories, Tag 0037, adjunction maps and formulas;
Derived Categories, Tag 0FND, naturality of adjunction comparisons.
The tensor-Hom consequence is agent-formulated, as specified by the DAG node
(blueprint: lem-coef-closed-adjunction-naturality).
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ u₁ u₂

open CategoryTheory Opposite

namespace CategoryTheory.ClosedAdjunctionComparison

/-- Evaluation is the inverse tensor-Hom transpose of the identity.
Source: Stacks Project, Categories, Tag 0037, adjunction maps;
agent-formulated tensor-Hom consequence
(blueprint: lem-coef-closed-adjunction-naturality). -/
def evaluation {C : Type u₁} [Category.{v₁} C]
    (tensor : C × C ⥤ C) (H : Cᵒᵖ × C ⥤ C)
    (θ : ∀ T X Y : C, (tensor.obj (T, X) ⟶ Y) ≃ (T ⟶ H.obj (op X, Y)))
    (X Y : C) : tensor.obj (H.obj (op X, Y), X) ⟶ Y :=
  (θ (H.obj (op X, Y)) X Y).symm (𝟙 (H.obj (op X, Y)))

/-- The specified comparison b is the transpose of tensor comparison, mapped
source evaluation, and the adjunction counit, in that order.
Source: Stacks Project, Categories, Tag 0037, adjunction maps;
agent-formulated tensor-Hom consequence
(blueprint: lem-coef-closed-adjunction-naturality). -/
def comparison
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (tensorC : C × C ⥤ C) (tensorD : D × D ⥤ D)
    (HC : Cᵒᵖ × C ⥤ C) (HD : Dᵒᵖ × D ⥤ D)
    (θC : ∀ T X Y : C, (tensorC.obj (T, X) ⟶ Y) ≃ (T ⟶ HC.obj (op X, Y)))
    (θD : ∀ T X Y : D, (tensorD.obj (T, X) ⟶ Y) ≃ (T ⟶ HD.obj (op X, Y)))
    (F : C ⥤ D) (G : D ⥤ C)
    (μ : ∀ X Y : C, tensorD.obj (F.obj X, F.obj Y) ≅ F.obj (tensorC.obj (X, Y)))
    (adj : F ⊣ G) (P : C) (N : D) :
    F.obj (HC.obj (op P, G.obj N)) ⟶ HD.obj (op (F.obj P), N) :=
  θD (F.obj (HC.obj (op P, G.obj N))) (F.obj P) N
    ((μ (HC.obj (op P, G.obj N)) P).hom ≫
      F.map (evaluation tensorC HC θC P (G.obj N)) ≫ adj.counit.app N)

/-- The specified comparison delta is the unit followed by G applied to b.
This is precisely the adjunction Hom-bijection convention of Stacks Tag 0037.
Source: Stacks Project, Categories, Tag 0037, formulas after Definition 4.24.1
(blueprint: lem-coef-closed-adjunction-naturality). -/
def adjointComparison
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (tensorC : C × C ⥤ C) (tensorD : D × D ⥤ D)
    (HC : Cᵒᵖ × C ⥤ C) (HD : Dᵒᵖ × D ⥤ D)
    (θC : ∀ T X Y : C, (tensorC.obj (T, X) ⟶ Y) ≃ (T ⟶ HC.obj (op X, Y)))
    (θD : ∀ T X Y : D, (tensorD.obj (T, X) ⟶ Y) ≃ (T ⟶ HD.obj (op X, Y)))
    (F : C ⥤ D) (G : D ⥤ C)
    (μ : ∀ X Y : C, tensorD.obj (F.obj X, F.obj Y) ≅ F.obj (tensorC.obj (X, Y)))
    (adj : F ⊣ G) (P : C) (N : D) :
    HC.obj (op P, G.obj N) ⟶ G.obj (HD.obj (op (F.obj P), N)) :=
  adj.unit.app (HC.obj (op P, G.obj N)) ≫
    G.map (comparison tensorC tensorD HC HD θC θD F G μ adj P N)

/-- Both evaluation-defined comparisons are natural in P and N.
Source: Stacks Project, Categories, Tag 0037, adjunction maps and naturality;
agent-formulated tensor-Hom consequence
(blueprint: lem-coef-closed-adjunction-naturality).

Proof plan:
1. Naturality of theta in T and the inverse-image definition of evaluation give
   theta-inverse(z) = evaluation composed with tensor(z, identity).
2. Naturality in X and Y, followed by injectivity of theta, gives the evaluation
   identity: tensor(H(a,g), identity) followed by evaluation equals
   tensor(identity,a) followed by evaluation and g. These two steps use only
   the category identity laws of def-nagata-category.
3. Uncurry the square for b. Naturality of mu at (H(a,Gv),identity), the evaluation
   identity in C, naturality of mu at (identity,a), and counit naturality give
   the equality of arrows from F(H(P,GN)) tensor F(P') to N'.
4. Apply theta in D to this equality. Its naturality in T gives F(H(a,Gv))
   followed by b on the left; its naturality in X and Y gives b followed by
   H(Fa,v) on the right. This proves the first asserted equality.
5. Unit naturality at H(a,Gv), the first equality, and functoriality of G give
   the second equality after substituting delta = unit followed by G(b).
   Unit and counit naturality and the Hom-bijection formula are those of
   lem-weil-pbc-adjunction-of-natural-bijection. No comparison is inverted. -/
theorem naturality
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
    (P P' : C) (N N' : D) (a : P' ⟶ P) (v : N ⟶ N') :
    (F.map (HC.map (Prod.mkHom a.op (G.map v))) ≫
        comparison tensorC tensorD HC HD θC θD F G μ adj P' N' =
      comparison tensorC tensorD HC HD θC θD F G μ adj P N ≫
        HD.map (Prod.mkHom (F.map a).op v)) ∧
    (HC.map (Prod.mkHom a.op (G.map v)) ≫
        adjointComparison tensorC tensorD HC HD θC θD F G μ adj P' N' =
      adjointComparison tensorC tensorD HC HD θC θD F G μ adj P N ≫
        G.map (HD.map (Prod.mkHom (F.map a).op v))) := by
  let A := HC.obj (op P, G.obj N)
  let A' := HC.obj (op P', G.obj N')
  let h : A ⟶ A' := HC.map (Prod.mkHom a.op (G.map v))
  let ev := evaluation tensorC HC θC P (G.obj N)
  let ev' := evaluation tensorC HC θC P' (G.obj N')
  -- Transposing evaluation gives the identity, by its definition.
  have hθev (X Y : C) :
      θC (HC.obj (op X, Y)) X Y (evaluation tensorC HC θC X Y) =
        𝟙 (HC.obj (op X, Y)) :=
    (θC (HC.obj (op X, Y)) X Y).apply_symm_apply _
  -- Both sides of the evaluation square transpose to h.
  have heval : tensorC.map (Prod.mkHom h (𝟙 P')) ≫ ev' =
      tensorC.map (Prod.mkHom (𝟙 A) a) ≫ ev ≫ G.map v := by
    apply (θC A P' (G.obj N')).injective
    calc
      _ = h := by
        simpa only [ev', A', Category.comp_id, hθev, op_id, ← prod_id,
          Functor.map_id] using
          hθC A' A P' P' (G.obj N') (G.obj N') ev' h (𝟙 P') (𝟙 (G.obj N'))
      _ = _ := by
        symm
        simpa only [ev, A, hθev, Category.id_comp] using
          hθC A A P P' (G.obj N) (G.obj N') ev (𝟙 A) a (G.map v)
  let k := (μ A P).hom ≫ F.map ev ≫ adj.counit.app N
  let k' := (μ A' P').hom ≫ F.map ev' ≫ adj.counit.app N'
  have hμ₁ : tensorD.map (Prod.mkHom (F.map h) (𝟙 (F.obj P'))) ≫ (μ A' P').hom =
      (μ A P').hom ≫ F.map (tensorC.map (Prod.mkHom h (𝟙 P'))) := by
    simpa only [Functor.map_id] using (hμ A A' P' P' h (𝟙 P')).symm
  have hμ₂ : (μ A P').hom ≫ F.map (tensorC.map (Prod.mkHom (𝟙 A) a)) =
      tensorD.map (Prod.mkHom (𝟙 (F.obj A)) (F.map a)) ≫ (μ A P).hom := by
    simpa only [Functor.map_id] using hμ A A P' P (𝟙 A) a
  -- The untransposed comparison square follows from evaluation and counit naturality.
  have hk : tensorD.map (Prod.mkHom (F.map h) (𝟙 (F.obj P'))) ≫ k' =
      tensorD.map (Prod.mkHom (𝟙 (F.obj A)) (F.map a)) ≫ k ≫ v := by
    calc
      _ = (μ A P').hom ≫
          F.map (tensorC.map (Prod.mkHom h (𝟙 P')) ≫ ev') ≫ adj.counit.app N' := by
        dsimp only [k']
        rw [← Category.assoc, hμ₁, Functor.map_comp]
        simp only [Category.assoc]
      _ = (μ A P').hom ≫
          F.map (tensorC.map (Prod.mkHom (𝟙 A) a) ≫ ev ≫ G.map v) ≫
            adj.counit.app N' := by rw [heval]
      _ = _ := by
        dsimp only [k]
        simp only [Functor.map_comp, Category.assoc]
        rw [adj.counit_naturality v, ← Category.assoc, ← Category.assoc, hμ₂]
        simp only [Category.assoc]
  have hb : F.map h ≫ comparison tensorC tensorD HC HD θC θD F G μ adj P' N' =
      comparison tensorC tensorD HC HD θC θD F G μ adj P N ≫
        HD.map (Prod.mkHom (F.map a).op v) := by
    change F.map h ≫ θD (F.obj A') (F.obj P') N' k' =
      θD (F.obj A) (F.obj P) N k ≫ HD.map (Prod.mkHom (F.map a).op v)
    calc
      _ = θD (F.obj A) (F.obj P') N'
          (tensorD.map (Prod.mkHom (F.map h) (𝟙 (F.obj P'))) ≫ k') := by
        symm
        simpa only [Category.comp_id, op_id, ← prod_id, Functor.map_id]
          using hθD (F.obj A') (F.obj A) (F.obj P') (F.obj P') N' N' k'
            (F.map h) (𝟙 (F.obj P')) (𝟙 N')
      _ = θD (F.obj A) (F.obj P') N'
          (tensorD.map (Prod.mkHom (𝟙 (F.obj A)) (F.map a)) ≫ k ≫ v) := by rw [hk]
      _ = _ := by
        simpa only [Category.id_comp] using
          hθD (F.obj A) (F.obj A) (F.obj P) (F.obj P') N N' k
            (𝟙 (F.obj A)) (F.map a) v
  refine ⟨hb, ?_⟩
  change h ≫ (adj.unit.app A' ≫
      G.map (comparison tensorC tensorD HC HD θC θD F G μ adj P' N')) = _
  rw [← Category.assoc, ← adj.unit_naturality h, Category.assoc, ← G.map_comp, hb,
    G.map_comp]
  simp only [adjointComparison, Category.assoc, A]

end CategoryTheory.ClosedAdjunctionComparison
