/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q51
-/
module

public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits

/-!
# Stationary legs of an eventually invertible telescope

Source: Stacks Project, Derived Categories, Tags 090Z, 0CRH and 0CRJ;
the explicit finite-sum argument in the DAG proof
(blueprint: lem-sfb-sequential-telescope-calculus).

The telescope is supplied with both of its last arrows. This is the distinguished
triangle used in `IsSequentialHomotopyColimit`, with its witnesses kept explicit
so that the conclusion concerns the actual supplied legs.
-/

@[expose] public section

universe v u

set_option autoImplicit false

open CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Every leg in the invertible tail of any chosen telescope triangle is an isomorphism.
Source: Stacks Project, Derived Categories, Tags 090Z (definition-derived-colimit),
0CRH (remark-uniqueness-derived-colimit), and 0CRJ (lemma-hocolim-subsequence),
with the explicit contraction from the DAG proof
(blueprint: lem-sfb-sequential-telescope-calculus).

Proof:
1. Put `f = 1 - s`, `j = ι_N`, and write `U_{i,k}` for the finite transition composite.
   Define `a_i = U_{i,N}` for `i ≤ N` and `a_i = U_{N,i}^{-1}` for `i > N`.
   These satisfy `u_i ≫ a_{i+1} = a_i`, including at `i = N`. The coproduct
   universal property (def-weil-pbc-category-colimit) gives `a : S ⟶ E_N`
   with `j ≫ a = 1` and `f ≫ a = 0`. Define `l : S ⟶ S` on the i-th summand
   as the sum of `U_{i,k} ≫ ι_k` for `i ≤ k < N` if `i < N`, zero if `i = N`,
   and the negative sum of `U_{k,i}^{-1} ≫ ι_k` for `N ≤ k < i` if `i > N`.
   Every sum is finite, and every inverse lies in the invertible tail.
2. The finite sums telescope on each summand, giving `f ≫ l = 1` and
   `l ≫ f = 1 - a ≫ j`. Check `i < N`, `i = N` and `i > N` separately,
   then apply coproduct extensionality (def-weil-pbc-category-colimit).
3. Triangle zero-composites (lem-weil-pbc-hom-into-triangle-exact) give
   `f ≫ p = 0` and `d ≫ f[1] = 0`, using rotation for the latter.
   Shift `f ≫ l = 1` to obtain `d = 0` (def-weil-triangulated-category).
4. Hom exactness (lem-weil-pbc-hom-out-of-triangle-exact, clause (i)) factors
   `a` as `p ≫ b`. Thus `j ≫ p ≫ b = 1`. For `h = 1 - b ≫ j ≫ p`,
   the identity `l ≫ f = 1 - a ≫ j` gives `p ≫ h = 0`. Clause (ii) factors
   `h` through `d`, so `h = 0`. Hence `j ≫ p` and `b` are inverse.
   Finally `f ≫ p = 0` gives `u_i ≫ λ_{i+1} = λ_i`; induction gives
   `U_{N,r} ≫ λ_r = λ_N`. For `r ≥ N`, the transition composite is invertible,
   so the actual leg `λ_r` is invertible. -/
theorem sequentialTelescope_leg_isIso
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [HasCountableCoproducts C]
    (E : ℕ → C) (u : ∀ r : ℕ, E r ⟶ E (r + 1))
    (s : (∐ E) ⟶ (∐ E))
    (hs : ∀ r : ℕ, Sigma.ι E r ≫ s = u r ≫ Sigma.ι E (r + 1))
    (H : C) (p : (∐ E) ⟶ H) (d : H ⟶ (∐ E)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (𝟙 (∐ E) - s) p d ∈ distTriang C)
    (N : ℕ) (hu : ∀ r : ℕ, N ≤ r → IsIso (u r)) :
    ∀ r : ℕ, N ≤ r → IsIso (Sigma.ι E r ≫ p) := by
  sorry

end CategoryTheory
