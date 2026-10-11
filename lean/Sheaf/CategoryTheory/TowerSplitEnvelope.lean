/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Functor.OfSequence

/-!
# Functorial split envelope of an inverse system

Source: literature/stacks-project/derived.tex, the agent-written replacement step
for Lemma Tag 070M (blueprint: lem-weil-tower-split-envelope).
-/

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Functorial finite-product split envelope of towers with its natural embedding
and split cokernel. The index `n` represents the positive integer `n + 1`.
The isomorphisms `e` identify each envelope term with the specified finite product;
the three component equations specify its transition projections, its action on
morphisms, and the embedding by composites of the original transition maps.

Source: literature/stacks-project/derived.tex, agent-written replacement step for
Lemma Tag 070M (lemma-difficulty-K-injectives).

Proof:
1. By `def-sp-abelian`, finite products are biproducts. Use their projections and
   injections and the composite transition maps of `def-weil-inverse-system`.
2. Define the action on morphisms componentwise. Comparing projections proves
   compatibility with transitions, preservation of identities and composition,
   and additivity by bilinearity (`def-weil-preadditive-category`).
3. The envelope transitions forget the last factor; inclusion with zero last
   component is a section (`def-weil-additive-category`).
4. The identities f(m+1,k) = f(m+1,m) followed by f(m,k) show that j is a tower
   morphism. Naturality of the original tower morphisms gives naturality of j.
   The last projection retracts each component of j, proving it monic.
   By `lem-weil-tower-category-levelwise-abelian`, cokernels are computed levelwise.
5. The automorphism subtracting f(m,k) times the last component from each earlier
   component carries j to the last summand injection. Its inverse adds these
   terms. Thus projection to the earlier factors after this automorphism is a
   cokernel, identifying C(m) with the product of the factors before m (zero at 1).
6. The induced cokernel transition is the map with components pr(k)-f(m,k)pr(m):
   this follows by expanding its composite with the preceding cokernel projection
   and cancelling using f(m+1,k)=f(m,k)f(m+1,m). Inclusion with last component
   zero is its section. Uniqueness of cokernels transports these sections to the
   chosen cokernel tower, proving it split.
(blueprint: lem-weil-tower-split-envelope) -/
theorem tower_split_envelope
    {C : Type u} [Category.{v} C] [Abelian C] :
    ∃ (E : (ℕᵒᵖ ⥤ C) ⥤ (ℕᵒᵖ ⥤ C)) (j : 𝟭 (ℕᵒᵖ ⥤ C) ⟶ E)
      (e : ∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ),
        (E.obj T).obj (Opposite.op n) ≅
          ∏ᶜ fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)),
      (∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ) (k : Fin (n + 1)),
        (E.obj T).map (homOfLE (Nat.le_succ n)).op ≫ (e T n).hom ≫
          Pi.π (fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)) k =
        (e T (n + 1)).hom ≫
          Pi.π (fun k : Fin (n + 1 + 1) ↦ T.obj (Opposite.op k.val)) k.castSucc) ∧
      (∀ (T T' : ℕᵒᵖ ⥤ C) (φ : T ⟶ T') (n : ℕ) (k : Fin (n + 1)),
        (E.map φ).app (Opposite.op n) ≫ (e T' n).hom ≫
          Pi.π (fun k : Fin (n + 1) ↦ T'.obj (Opposite.op k.val)) k =
        (e T n).hom ≫ Pi.π (fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)) k ≫
          φ.app (Opposite.op k.val)) ∧
      (∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ) (k : Fin (n + 1)),
        (j.app T).app (Opposite.op n) ≫ (e T n).hom ≫
          Pi.π (fun k : Fin (n + 1) ↦ T.obj (Opposite.op k.val)) k =
        T.map (homOfLE (Nat.le_of_lt_succ k.isLt)).op) ∧
      (∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ),
        IsSplitEpi ((E.obj T).map (homOfLE (Nat.le_succ n)).op)) ∧
      (∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ), Mono ((j.app T).app (Opposite.op n))) ∧
      (∀ (T T' : ℕᵒᵖ ⥤ C) (φ ψ : T ⟶ T'), E.map (φ + ψ) = E.map φ + E.map ψ) ∧
      (∀ (T : ℕᵒᵖ ⥤ C) (n : ℕ),
        IsSplitEpi ((cokernel (j.app T)).map (homOfLE (Nat.le_succ n)).op)) := by
  sorry

end CategoryTheory
