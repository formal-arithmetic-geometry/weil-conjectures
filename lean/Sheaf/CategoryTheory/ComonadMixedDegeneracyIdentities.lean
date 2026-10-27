/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group O1
-/
module

public import Sheaf.CategoryTheory.NaturalTransportInduction

/-! # Mixed and degeneracy identities for the raw comonad operators

Source: literature/stacks-project/simplicial.tex, Example 0G5M (example-godement)
and Lemma 0G5N (lemma-godement), proof of (1)(b)--(e)
(blueprint: lem-trf-comonad-mixed-degeneracy-identities).

The face and degeneracy transformations below are actual recursive whiskerings of the
specified counit and comultiplication. No simplicial object is assumed or chosen.
The index of a face is its source degree; its degree-zero extension is the counit.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.NaturalTransport

/-- The transformation `1_i ⋆ e ⋆ 1_(n-i)` from `T^(n+1)` to `T^n`.
At index zero, apply `e` outside the remaining powers. At a successor index, whisker
that same construction on the outside by `T`. This is exactly insertion in the
specified position, counted from the outside; naturality is part of its type.
The degree-zero extension is the counit itself.

Source: Stacks, Example 0G5M and Lemma 0G5N, proof of (1)(b)--(e)
(blueprint: lem-trf-comonad-mixed-degeneracy-identities). -/
def comonadFace {C : Type u} [Category.{v} C] (T : C ⥤ C) (e : T ⟶ 𝟭 C) :
    (n : ℕ) → Fin (n + 1) → (power T (n + 1) ⟶ power T n)
  | 0, _ => e
  | n + 1, i => Fin.cases
      (Functor.whiskerLeft (power T (n + 1)) e)
      (fun j ↦ Functor.whiskerRight (comonadFace T e n j) T) i

/-- The transformation `1_i ⋆ c ⋆ 1_(n-i)` from `T^(n+1)` to `T^(n+2)`.
At index zero, apply `c` outside the remaining powers. At a successor index, whisker
that same construction on the outside by `T`. Thus these are the displayed raw
transformations, with their naturality supplied by whiskering.

Source: Stacks, Example 0G5M and Lemma 0G5N, proof of (1)(b)--(e)
(blueprint: lem-trf-comonad-mixed-degeneracy-identities). -/
def comonadDegeneracy {C : Type u} [Category.{v} C] (T : C ⥤ C)
    (c : T ⟶ T ⋙ T) :
    (n : ℕ) → Fin (n + 1) → (power T (n + 1) ⟶ power T (n + 2))
  | 0, _ => c
  | n + 1, i => Fin.cases
      (Functor.whiskerLeft (power T (n + 1)) c)
      (fun j ↦ Functor.whiskerRight (comonadDegeneracy T c n j) T) i

/-- The mixed identities, both counit cancellations, and the double degeneracy identity
hold for the specified whiskered maps themselves. In the first two clauses the source
node's `n` is `n + 2`; in the last two it is `n + 1`. In the first clause the larger
index is `j + 1`; in the second clause the face index is `i + 1`.

Source: Stacks, Example 0G5M and Lemma 0G5N, proof of (1)(b)--(e)
(blueprint: lem-trf-comonad-mixed-degeneracy-identities).

Proof plan:
1. Use def-trf-endofunctor-powers. Induction gives `T^a T^b = T^(a+b)`, including
   zero powers. The recursive whiskerings have components `T^i(e_(T^(n-i) x))`
   and `T^i(c_(T^(n-i) x))`. Naturality follows by applying `T^i` to naturality of
   `e` or `c` at `T^(n-i)(f)`; it is already encoded in these natural transformations.
2. For the first mixed identity, in the original indices put `k = j-i-1` and
   `r = n-j-1`. Remove the outer `T^i` and evaluate at `T^r x`. Apply
   lem-amb-natural-transformation-whisker-exchange, namely
   Functor.whiskerLeft_comp_whiskerRight, with `η = 1_k ⋆ c` and `θ = e`.
   Both composites reduce to `e ⋆ 1_k ⋆ c`; restore the outer and inner powers.
3. For the second mixed identity put `k = i-j-2` and `r = n-i`. Remove `T^j`,
   evaluate at `T^r x`, and use the same exchange with `η = 1_k ⋆ e`, `θ = c`.
   Both sides reduce to `c ⋆ 1_k ⋆ e`; restore the powers.
4. For either cancellation put `r = n-1-j`. Expansion and functoriality of `T^j`
   leave respectively `(e ⋆ 1_1) ∘ c` and `(1_1 ⋆ e) ∘ c` in the middle.
   The two counit equations replace these by the identity; whiskering preserves it.
5. For distinct degeneracy indices put `k = j-i-1` and `r = n-j-1`, remove `T^i`
   and evaluate at `T^r x`. Exchange with `η = 1_k ⋆ c`, `θ = c` reduces both
   composites to `c ⋆ 1_k ⋆ c`. Restore the powers.
6. For equal indices put `r = n-1-i`. Both sides are `T^i` applied at `T^r x` to
   the two coassociativity composites. Apply the assumed coassociativity equation.
   This also covers `n = 1`, `i = j = 0` in the original indices. -/
theorem comonad_mixed_degeneracy_identities
    {C : Type u} [Category.{v} C]
    (T : C ⥤ C) (e : T ⟶ 𝟭 C) (c : T ⟶ T ⋙ T)
    (h₁ : c ≫ Functor.whiskerRight e T ≫ (Functor.leftUnitor T).hom = 𝟙 T)
    (h₂ : c ≫ Functor.whiskerLeft T e ≫ (Functor.rightUnitor T).hom = 𝟙 T)
    (h₃ : c ≫ Functor.whiskerRight c T ≫ (Functor.associator T T T).hom =
      c ≫ Functor.whiskerLeft T c) :
    (∀ (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)), i ≤ j.castSucc →
      comonadDegeneracy T c (n + 1) j.succ ≫ comonadFace T e (n + 2) i.castSucc =
        comonadFace T e (n + 1) i ≫ comonadDegeneracy T c n j) ∧
    (∀ (n : ℕ) (i : Fin (n + 2)) (j : Fin (n + 1)), j.castSucc < i →
      comonadDegeneracy T c (n + 1) j.castSucc ≫ comonadFace T e (n + 2) i.succ =
        comonadFace T e (n + 1) i ≫ comonadDegeneracy T c n j) ∧
    (∀ (n : ℕ) (j : Fin (n + 1)),
      comonadDegeneracy T c n j ≫ comonadFace T e (n + 1) j.castSucc =
          𝟙 (power T (n + 1)) ∧
        comonadDegeneracy T c n j ≫ comonadFace T e (n + 1) j.succ =
          𝟙 (power T (n + 1))) ∧
    (∀ (n : ℕ) (i j : Fin (n + 1)), i ≤ j →
      comonadDegeneracy T c n j ≫ comonadDegeneracy T c (n + 1) i.castSucc =
        comonadDegeneracy T c n i ≫ comonadDegeneracy T c (n + 1) j.succ) := by
  sorry

end CategoryTheory.NaturalTransport
