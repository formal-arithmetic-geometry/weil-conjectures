/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.ProEtalePointComponentsMaps
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Affine evaluation of the point left Kan extension

Source: Bhatt–Scholze, Lemma 4.2.13(1), proof; RefactorInstruction, Section 4,
Lemma point-eval, first paragraph of proof
(blueprint: lem-weil-pbc-point-lan-affine-evaluation).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Weak contractibility, expressed by sections of epimorphisms of set sheaves.
Source: Bhatt–Scholze, Section 4.2; RefactorInstruction, Lemma point-eval
(blueprint: lem-weil-pbc-point-lan-affine-evaluation). -/
def PointLanWeaklyContractible (X : Scheme.{u}) (U : X.ProEt) : Prop :=
  ∀ (F G : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : F ⟶ G),
    Epi f → Function.Surjective (f.hom.app (op U))

/-- The actual connected-component quotient, with its quotient topology, bundled as profinite.
The topological structure proofs are the recorded component-map theorem.
Source: Bhatt–Scholze, Lemma 4.2.13(1); RefactorInstruction, Lemma point-eval
(blueprint: lem-weil-pbc-point-lan-affine-evaluation). -/
def pointLanComponents (X : Scheme.{u}) (U : X.ProEt) (hU : IsAffine U.left)
    (wU : PointLanWeaklyContractible X U) : Profinite.{u} :=
  @Profinite.of (ConnectedComponents U.left) _
    ((proEtale_point_components_maps X).1 U hU wU).1
    ((proEtale_point_components_maps X).1 U hU wU).2.1
    ((proEtale_point_components_maps X).1 U hU wU).2.2

/-- Packaging of the evaluation formula in a specified coefficient category.
A pointwise Kan extension is supplied with its unit, rather than with a choice of colimits.
The normalization on every Kan cocone map specifies the evaluation comparison.
Naturality is simultaneous in coefficient sheaves and in weakly contractible affine objects.
The last clause says exactly that the restriction cone for every finite coproduct is a
product cone, also for an empty index type.
Source: Bhatt–Scholze, Lemma 4.2.13(1); RefactorInstruction, Lemma point-eval
(blueprint: lem-weil-pbc-point-lan-affine-evaluation). -/
def PointLanAffineEvaluationProperty (X : Scheme.{u}) (C : Type w) [Category.{v} C] :
    Prop :=
  ∃ b : ∀ (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U)
      (S : Profinite.{u}),
      (U ⟶ (profiniteToProEtOf X).obj S) ≃ (pointLanComponents X U hU wU ⟶ S),
    (∀ (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U)
      (S T : Profinite.{u}) (g : S ⟶ T) (f : U ⟶ (profiniteToProEtOf X).obj S),
      b U hU wU T (f ≫ (profiniteToProEtOf X).map g) = b U hU wU S f ≫ g) ∧
    (∀ (U V : X.ProEt) (hU : IsAffine U.left) (hV : IsAffine V.left)
      (wU : PointLanWeaklyContractible X U) (wV : PointLanWeaklyContractible X V)
      (a : V ⟶ U) (S : Profinite.{u}) (f : U ⟶ (profiniteToProEtOf X).obj S),
      b V hV wV S (a ≫ f) =
        (ConcreteCategory.ofHom
          ⟨a.left.continuous.connectedComponentsMap,
          a.left.continuous.connectedComponentsMap_continuous⟩ :
          pointLanComponents X V hV wV ⟶ pointLanComponents X U hU wU) ≫
          b U hU wU S f) ∧
    (∃ e : ∀ (F : Sheaf (coherentTopology Profinite.{u}) C)
        (P : X.ProEtᵒᵖ ⥤ C) (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P),
        (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension →
        ∀ (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U),
          P.obj (op U) ≅ F.obj.obj (op (pointLanComponents X U hU wU)),
      (∀ (F : Sheaf (coherentTopology Profinite.{u}) C) (P : X.ProEtᵒᵖ ⥤ C)
        (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P)
        (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
        (U : X.ProEt) (hU : IsAffine U.left) (wU : PointLanWeaklyContractible X U)
        (S : Profinite.{u}) (f : U ⟶ (profiniteToProEtOf X).obj S),
        η.app (op S) ≫ P.map f.op ≫ (e F P η hP U hU wU).hom =
          F.obj.map (b U hU wU S f).op) ∧
      (∀ (F G : Sheaf (coherentTopology Profinite.{u}) C)
        (P Q : X.ProEtᵒᵖ ⥤ C)
        (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P)
        (θ : G.obj ⟶ (profiniteToProEtOf X).op ⋙ Q)
        (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
        (hQ : (Functor.LeftExtension.mk Q θ).IsPointwiseLeftKanExtension)
        (α : F ⟶ G) (β : P ⟶ Q)
        (_hβ : η ≫ Functor.whiskerLeft (profiniteToProEtOf X).op β = α.hom ≫ θ)
        (U V : X.ProEt) (hU : IsAffine U.left) (hV : IsAffine V.left)
        (wU : PointLanWeaklyContractible X U) (wV : PointLanWeaklyContractible X V)
        (a : V ⟶ U),
        P.map a.op ≫ β.app (op V) ≫ (e G Q θ hQ V hV wV).hom =
          (e F P η hP U hU wU).hom ≫
            F.obj.map (ConcreteCategory.ofHom
              ⟨a.left.continuous.connectedComponentsMap,
              a.left.continuous.connectedComponentsMap_continuous⟩ :
              pointLanComponents X V hV wV ⟶ pointLanComponents X U hU wU).op ≫
            α.hom.app (op (pointLanComponents X V hV wV)))) ∧
    (∀ (F : Sheaf (coherentTopology Profinite.{u}) C) (P : X.ProEtᵒᵖ ⥤ C)
      (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P)
      (_ : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
      (I : Type u) [Finite I] (U : I → X.ProEt),
      (∀ i : I, IsAffine (U i).left) →
      (∀ i : I, PointLanWeaklyContractible X (U i)) →
      ∃ c : Cofan U, Nonempty (IsColimit c) ∧
        Nonempty (IsLimit (Fan.mk (P.obj (op c.pt)) (fun i ↦ P.map (c.inj i).op))))

/-- The point left Kan presheaf on a weakly contractible affine is evaluation on its
profinite connected-component quotient. The identifications are canonical, natural in
both arguments, preserve the coefficient operations, and send finite disjoint unions
(including the empty one) to products.

Source: Bhatt–Scholze, Lemma 4.2.13(1), proof, first two sentences;
RefactorInstruction, Section 4, Lemma point-eval, proof, first paragraph
(blueprint: lem-weil-pbc-point-lan-affine-evaluation).

Proof for stage 3:
1. Use lem-weil-pbc-proetale-point-components-maps to obtain the profinite component
   quotient and the natural correspondence between maps into X[S] and maps into S.
2. For T = pi_0(U), let q correspond to the identity on T. Every map U → X[S]
   corresponds to a unique map T → S. Thus (T,q) is terminal in the Kan index,
   whose arrows reverse the maps of profinite targets. Its colimit is F(T): the
   cocone maps are F(g), and compatibility forces every cocone to factor uniquely
   through its component at (T,q). This works in all three coefficient categories.
3. Components of a finite disjoint union form the finite coproduct of the component
   spaces. The sheaf condition on the finite jointly surjective coproduct cover gives
   the product cone, also for the empty family. Precomposition gives naturality in U;
   naturality of a sheaf morphism gives naturality in F. All cocone maps and the
   resulting isomorphisms are morphisms of the indicated coefficient category. -/
theorem point_lan_affine_evaluation (X : Scheme.{u}) :
    PointLanAffineEvaluationProperty X (Type (u + 1)) ∧
    PointLanAffineEvaluationProperty X AddCommGrpCat.{u + 1} ∧
    PointLanAffineEvaluationProperty X CommRingCat.{u + 1} := by
  sorry

end AlgebraicGeometry.ProEtale
