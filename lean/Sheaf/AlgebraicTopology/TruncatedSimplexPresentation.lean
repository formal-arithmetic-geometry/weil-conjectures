module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import Sheaf.AlgebraicTopology.PureCofaceWordRelations

/-!
# Recognition and generation in the truncated simplex category

Source: Stacks Project, simplicial.tex, Tags 0166, 0168, 016B and Definition 0180,
bounded-degree form (blueprint: lem-sfb-truncated-simplex-presentation).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory Opposite

namespace CategoryTheory.SimplicialObject.Truncated

/-- Face and degeneracy identities in degrees at most `N` give a unique truncated
simplicial object. All arrows are generated within those degrees, surjections use
only codegeneracies, and naturality can be tested on the generators.

The object family is indexed by the actual objects of the opposite truncated
simplex category. The equality `F.obj = U` fixes those objects; `HEq` expresses
agreement of generator maps after transport along this equality. The two
`multiplicativeClosure` clauses mean finite composable words, including identities,
in the truncated category itself, so every intermediate degree is at most `N`.

Source: Stacks Project, simplicial.tex, Tags 0166, 0168, 016B and Definition 0180,
bounded-degree form (blueprint: lem-sfb-truncated-simplex-presentation).

Proof:
1. For an ordinal map from degree `a` to degree `b`, induct on `a+b`. Remove a
   missing target value by factoring off a coface. Otherwise the map is surjective;
   remove an adjacent repeated value by factoring off a codegeneracy. A bijective
   monotone map is the identity. Intermediate degrees never exceed `max a b`.
   Beginning with a surjection uses only the second reduction and codegeneracies.
2. In a generator word, interchange each adjacent coface followed by codegeneracy
   using a mixed relation. The two middle cases cancel. Every other interchange
   lowers the intervening peak by two. No negative degree appears: at degree zero
   only cancellation is possible. Length, then the number of coface-before-
   codegeneracy pairs, decreases lexicographically. The result is a surjective
   block followed by an injective block, still in degrees at most `N`.
3. Equal composites have the same ordered image, hence the same middle ordinal
   and the same injective and surjective factors. Apply
   lem-sfb-pure-coface-word-relations and lem-sfb-pure-codegeneracy-word-relations
   to the two blocks. Those transformations remain between the block endpoints.
   Together with step 2 this gives all relations needed within the bound.
4. Evaluate the word from step 1 contravariantly using `d` and `s`. The identities
   preserve evaluations in every context, so steps 2 and 3 make this independent
   of the chosen word. Concatenation and the empty word give functoriality and
   identity preservation. Generator values are prescribed, and step 1 implies
   uniqueness. This is the functor notion of def-weil-pbc-simplicial-coskeleton.
5. Naturality holds on identities and is preserved under composition by
   associativity. Step 1 therefore extends naturality on faces and degeneracies
   to every arrow. Conversely every natural family commutes with each generator.
   For `N=0` there are no generators and the only arrow is the identity. -/
theorem truncated_simplex_presentation
    {C : Type u} [Category.{v} C] (N : ℕ)
    (U : (SimplexCategory.Truncated N)ᵒᵖ → C)
    (d : ∀ (n : ℕ) (hn : n + 1 ≤ N) (_i : Fin (n + 2)),
      U (op ⟨SimplexCategory.mk (n + 1), hn⟩) ⟶
        U (op ⟨SimplexCategory.mk n, by change n ≤ N; omega⟩))
    (s : ∀ (n : ℕ) (hn : n + 1 ≤ N) (_i : Fin (n + 1)),
      U (op ⟨SimplexCategory.mk n, by change n ≤ N; omega⟩) ⟶
        U (op ⟨SimplexCategory.mk (n + 1), hn⟩))
    (hdd : ∀ (n : ℕ) (hn : n + 2 ≤ N) (i j : Fin (n + 2)), i ≤ j →
      d (n + 1) hn j.succ ≫ d n (by omega) i =
        d (n + 1) hn i.castSucc ≫ d n (by omega) j)
    (hds_lt : ∀ (n : ℕ) (hn : n + 2 ≤ N) (i : Fin (n + 2)) (j : Fin (n + 1)),
      i ≤ j.castSucc →
      s (n + 1) hn j.succ ≫ d (n + 1) hn i.castSucc =
        d n (by omega) i ≫ s n (by omega) j)
    (hds_self : ∀ (n : ℕ) (hn : n + 1 ≤ N) (i : Fin (n + 1)),
      s n hn i ≫ d n hn i.castSucc = 𝟙 _)
    (hds_succ : ∀ (n : ℕ) (hn : n + 1 ≤ N) (i : Fin (n + 1)),
      s n hn i ≫ d n hn i.succ = 𝟙 _)
    (hds_gt : ∀ (n : ℕ) (hn : n + 2 ≤ N) (i : Fin (n + 2)) (j : Fin (n + 1)),
      j.castSucc < i →
      s (n + 1) hn j.castSucc ≫ d (n + 1) hn i.succ =
        d n (by omega) i ≫ s n (by omega) j)
    (hss : ∀ (n : ℕ) (hn : n + 2 ≤ N) (i j : Fin (n + 1)), i ≤ j →
      s n (by omega) j ≫ s (n + 1) hn i.castSucc =
        s n (by omega) i ≫ s (n + 1) hn j.succ) :
    (∃! F : SimplicialObject.Truncated C N,
      F.obj = U ∧
      (∀ (n : ℕ) (hn : n + 1 ≤ N) (i : Fin (n + 2)),
        HEq (F.map (SimplexCategory.Truncated.δ N i (by change n ≤ N; omega) hn).op)
          (d n hn i)) ∧
      (∀ (n : ℕ) (hn : n + 1 ≤ N) (i : Fin (n + 1)),
        HEq (F.map (SimplexCategory.Truncated.σ N i hn (by change n ≤ N; omega)).op)
          (s n hn i))) ∧
    (∀ (a b : SimplexCategory.Truncated N) (f : a ⟶ b),
      MorphismProperty.multiplicativeClosure
        (fun _ _ g ↦
          (∃ (n : ℕ) (hn : n + 1 ≤ N) (i : Fin (n + 2)),
            Arrow.mk g = Arrow.mk
              (SimplexCategory.Truncated.δ N i (by change n ≤ N; omega) hn)) ∨
          (∃ (n : ℕ) (hn : n + 1 ≤ N) (i : Fin (n + 1)),
            Arrow.mk g = Arrow.mk
              (SimplexCategory.Truncated.σ N i hn (by change n ≤ N; omega)))) f) ∧
    (∀ (a b : SimplexCategory.Truncated N) (f : a ⟶ b),
      Function.Surjective f.hom.toOrderHom →
      MorphismProperty.multiplicativeClosure
        (fun _ _ g ↦ ∃ (n : ℕ) (hn : n + 1 ≤ N) (i : Fin (n + 1)),
          Arrow.mk g = Arrow.mk
              (SimplexCategory.Truncated.σ N i hn (by change n ≤ N; omega))) f) ∧
    (∀ (F G : SimplicialObject.Truncated C N) (η : ∀ a, F.obj a ⟶ G.obj a),
      (∀ (a b : (SimplexCategory.Truncated N)ᵒᵖ) (f : a ⟶ b),
        F.map f ≫ η b = η a ≫ G.map f) ↔
      (∀ (n : ℕ) (hn : n + 1 ≤ N) (i : Fin (n + 2)),
        F.map (SimplexCategory.Truncated.δ N i (by change n ≤ N; omega) hn).op ≫
            η (op ⟨SimplexCategory.mk n, by change n ≤ N; omega⟩) =
          η (op ⟨SimplexCategory.mk (n + 1), hn⟩) ≫
            G.map (SimplexCategory.Truncated.δ N i (by change n ≤ N; omega) hn).op) ∧
      (∀ (n : ℕ) (hn : n + 1 ≤ N) (i : Fin (n + 1)),
        F.map (SimplexCategory.Truncated.σ N i hn (by change n ≤ N; omega)).op ≫
            η (op ⟨SimplexCategory.mk (n + 1), hn⟩) =
          η (op ⟨SimplexCategory.mk n, by change n ≤ N; omega⟩) ≫
            G.map (SimplexCategory.Truncated.σ N i hn (by change n ≤ N; omega)).op)) := by
  sorry

end CategoryTheory.SimplicialObject.Truncated
