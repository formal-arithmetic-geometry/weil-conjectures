/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Paper.ProfiniteTestObjectFunctor
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Sheaf.Paper.ProEtalePointComponentsMaps

/-! # Finite coproducts for the point Kan presheaf -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

/-- Finite affine coproducts induce product cones for point Kan extensions.

Source: Bhatt–Scholze, Lemma 4.2.13(1), proof, component-factorization and sheaf
argument; RefactorInstruction, Section 4, Lemma point-eval, finite coproduct clause.
(blueprint: lem-weil-pbc-point-lan-affine-evaluation-finite-products).

Proof in words:
1. Let W be the scheme coproduct of the U i, with structure map to X induced by
   their structure maps. Weak etaleness is Zariski local on the source, so W is an
   object of X.ProEt. The scheme coproduct universal property gives a colimit
   cofan c in X.ProEt as well: its unique descents commute with the maps to X
   because they do so on each summand.
2. The component-map theorem supplies profinite T i = pi_0(U i) and natural
   equivalences b_i(S) between maps U i → X[S] and maps T i → S. Let T be the
   finite profinite coproduct of the T i, with inclusions j_i. For every S, the
   coproduct universal properties give a natural equivalence b_W(S) between
   maps W → X[S] and maps T → S: the latter is the unique map whose composites
   with j_i are b_i(S)(c.inj i ≫ f). Consequently b_W(S)(f) restricts along j_i
   to b_i(S)(c.inj i ≫ f).
3. For either V = U i or V = W, let q_V : V → X[T_V] correspond to the identity
   under its equivalence. A map f : V → X[S] factors uniquely as q_V followed
   by X[b_V(S)(f)]. Thus (T_V,q_V) is terminal in the costructured-arrow index
   for left Kan extension along X[-].op. Its cocone leg is an isomorphism by
   the pointwise Kan hypothesis. Its inverse gives e_V : P(V) ≅ F(T_V), with
   normalization eta_S ≫ P(f.op) ≫ e_V.hom = F(b_V(S)(f).op). To compare a
   summand inclusion, precompose with every Kan cocone leg at W. The displayed
   restriction formula for b_W and the normalization identify both composites,
   proving P((c.inj i).op) ≫ e_i.hom = e_W.hom ≫ F(j_i.op).
4. A coherent sheaf on profinite spaces preserves finite products on the opposite
   category, by Mathlib's Presheaf.instPreservesFiniteProductsOppositeVal. Applying
   F to the opposite of the coproduct cofan of the T i gives a product cone.
   The isomorphisms e_W and e_i and the preceding identity identify it with the
   asserted restriction cone, which is therefore a limit. For the empty index,
   W and T are initial, the same terminal-index argument still applies, and the
   empty product preserved by F makes the cone point terminal. For a singleton,
   both coproducts are their sole summands and the restriction is an isomorphism.
No affine evaluation theorem for W, nor weak contractibility of W, is used. -/
theorem point_lan_finite_products (X : Scheme.{u}) (C : Type w) [Category.{v} C]
    (F : Sheaf (coherentTopology Profinite.{u}) C) (P : X.ProEtᵒᵖ ⥤ C)
    (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P)
    (hP : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
    (I : Type u) [Finite I] (U : I → X.ProEt)
    (ha : ∀ i, IsAffine (U i).left)
    (hw : ∀ i,
      ∀ (A B : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))) (f : A ⟶ B),
        Epi f → Function.Surjective (f.hom.app (op (U i)))) :
    ∃ c : Cofan U, Nonempty (IsColimit c) ∧
      Nonempty (IsLimit (Fan.mk (P.obj (op c.pt)) (fun i ↦ P.map (c.inj i).op))) := by
  sorry

end AlgebraicGeometry.ProEtale
