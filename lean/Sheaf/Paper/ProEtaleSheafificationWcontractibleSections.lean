/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Sheaf.Paper.PointLanAffineEvaluation
public import Mathlib.CategoryTheory.Sites.LeftExact
import Sheaf.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Sheaf.Paper.SiteSheafificationSectionsLocal
import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory

/-!
# Sheafification on weakly contractible affine objects

Source: Bhatt–Scholze, Section 4.2, Lemma 4.2.13(1); RefactorInstruction,
proof of Lemma point-eval
(blueprint: lem-weil-pbc-proetale-sheafification-wcontractible-sections).
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite

namespace AlgebraicGeometry.ProEtale

/-- The sheafification unit for the point Kan presheaf is invertible on weakly
contractible affines, naturally in the affine and in the coefficient sheaf.
The compatibility equation specifies the Kan-induced map associated to a coefficient
sheaf morphism. All equations are in the coefficient category, so they respect its
operations. This is a packaging of the conclusion, not an additional hypothesis.

Source: Bhatt–Scholze, Lemma 4.2.13(1); RefactorInstruction, proof of Lemma point-eval
(blueprint: lem-weil-pbc-proetale-sheafification-wcontractible-sections). -/
def PointLanSheafificationProperty (X : Scheme.{u}) (C : Type w) [Category.{v} C]
    [HasWeakSheafify (Scheme.ProEt.topology X) C] : Prop :=
  ∀ (F : Sheaf (coherentTopology Profinite.{u}) C) (P : X.ProEtᵒᵖ ⥤ C)
    (η : F.obj ⟶ (profiniteToProEtOf X).op ⋙ P),
    (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension →
    ∀ (U : X.ProEt), IsAffine U.left → PointLanWeaklyContractible X U →
      IsIso ((toSheafify (Scheme.ProEt.topology X) P).app (op U)) ∧
      (∀ (V : X.ProEt), IsAffine V.left → PointLanWeaklyContractible X V →
        ∀ f : V ⟶ U,
          P.map f.op ≫ (toSheafify (Scheme.ProEt.topology X) P).app (op V) =
            (toSheafify (Scheme.ProEt.topology X) P).app (op U) ≫
              (sheafify (Scheme.ProEt.topology X) P).map f.op) ∧
      (∀ (G : Sheaf (coherentTopology Profinite.{u}) C) (Q : X.ProEtᵒᵖ ⥤ C)
        (θ : G.obj ⟶ (profiniteToProEtOf X).op ⋙ Q),
        (Functor.LeftExtension.mk Q θ).IsPointwiseLeftKanExtension →
        ∀ (α : F ⟶ G) (β : P ⟶ Q),
          η ≫ Functor.whiskerLeft (profiniteToProEtOf X).op β = α.hom ≫ θ →
          β.app (op U) ≫ (toSheafify (Scheme.ProEt.topology X) Q).app (op U) =
            (toSheafify (Scheme.ProEt.topology X) P).app (op U) ≫
              (sheafifyMap (Scheme.ProEt.topology X) β).app (op U))

/-- Sheafification preserves the point Kan presheaf's sections on every weakly
contractible affine, for sets, abelian groups and commutative rings. The canonical
isomorphisms are natural in both variables and preserve the coefficient operations.

Source: Bhatt–Scholze, Section 4.2, Lemma 4.2.13(1); RefactorInstruction,
proof of Lemma point-eval
(blueprint: lem-weil-pbc-proetale-sheafification-wcontractible-sections).

Proof for stage 3 (repair of the finite-refinement argument):
1. The point Kan evaluation lemma gives the finite restriction-product comparison
   only for families of weakly contractible affines, including the empty family.
   We will apply it to clopen pieces of U, not to arbitrary affine covering pieces.
2. Given any covering of U, its covering criterion gives finitely many affine
   arrows V_i → U refining it. Put V = coproduct V_i. Finite-coproduct evaluation
   and subcanonicity identify h_V with the coproduct of the h_{V_i}. The cover makes
   h_V → h_U epi by sheaf uniqueness. Weak contractibility lifts id_U to a section
   sigma : U → V. Put W_i = sigma^{-1}(V_i). These are disjoint clopen subschemes
   with coproduct U; each maps to V_i over U and is affine because U is affine.
   Each W_i is weakly contractible: for a set-sheaf epi A → B and b in B(W_i),
   write U = W_i disjoint-union Z and use finite-coproduct evaluation to glue b
   (in the B summand) with the terminal section on Z into (B coproduct 1)(U).
   The morphism A coproduct 1 → B coproduct 1 is epi. Lift on U using its weak
   contractibility, then restrict to W_i. Disjointness and pullback stability of
   sheaf coproducts force this restriction into A, giving the desired lift of b.
   Thus the W_i give a finite weakly contractible affine refinement. No covering
   arrow V_i is assumed weakly contractible. Empty pieces and the empty U are allowed.
3. Local sections of sheafification give representatives on a covering of U.
   Form the W_i of step 2 and restrict the representatives along W_i → V_i.
   Step 1, now with all its hypotheses verified, combines these into s in P(U),
   using the canonical isomorphism from the coproduct of W_i to U. The unit's
   naturality and sheaf uniqueness give eta(s) = t, proving surjectivity.
   For injectivity, equality after sheafification gives local equality on a cover.
   Apply step 2 to that cover; the restrictions of x and y agree on every W_i.
   Injectivity of the restriction-product comparison for this family gives x = y.
4. For algebraic coefficients, perform operations on local representatives. Local
   equality makes them well-defined and sheaf uniqueness glues them. Identities hold
   locally, and the universal property identifies this with algebra sheafification.
   Thus the bijection is an algebra isomorphism. Naturality of the unit gives both
   displayed naturality equations. -/
theorem proEtale_sheafification_wcontractible_sections (X : Scheme.{u}) :
    PointLanSheafificationProperty X (Type (u + 1)) ∧
    PointLanSheafificationProperty X AddCommGrpCat.{u + 1} ∧
    PointLanSheafificationProperty X CommRingCat.{u + 1} := by
  sorry

end AlgebraicGeometry.ProEtale
