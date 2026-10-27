module

public import Sheaf.AlgebraicTopology.PureCofaceWord

/-!
# Completeness of the pure coface relations

Source: Stacks, simplicial.tex, Tags 0167(1) and 0168, omitted pure-coface normal-form
input, with the proof supplied in the DAG (blueprint: lem-sfb-pure-coface-word-relations).
-/

@[expose] public section

set_option autoImplicit false

namespace SimplexCategory.CofaceWord

/-- Equal-valued raw coface words are connected using only adjacent coface relations,
in either direction, with every degree between their endpoints.

Source: Stacks, Tags 0167(1), 0168, omitted pure-coface input; the following proof is
supplied by the DAG (blueprint: lem-sfb-pure-coface-word-relations).

Proof:
1. Write a word from degree `a` to degree `b` in outermost-first order with indices
   `j₁,...,jₖ`, where `k = b - a`; the intermediate degrees are forced. The empty
   word is the only case `k = 0`. Each coface sends `x` to `x` below its omitted
   index and to `x + 1` otherwise, by def-weil-pbc-simplicial-set.
2. Replace an adjacent outer index `j` and inner index `i < j` by outer `i` and
   inner `j - 1`. This is typed, keeps the same intermediate degree, and preserves
   evaluation by lem-weil-pbc-simplex-face-face-identity, namely δ_comp_δ. The sum
   of all indices decreases exactly by one.
3. Strong induction on this nonnegative sum gives a finite reduction to a word
   with nondecreasing indices in outermost-first order: either a decrease permits
   step 2 and the induction hypothesis, or the word is already ordered. At sum
   zero all indices are zero. All moves retain the entire degree sequence.
4. For an ordered word, the omitted vertices are the strictly increasing list
   `j₁,j₂+1,...,jₖ+k-1`. Induct on length: remove the outer coface, use the tail's
   omitted list, and observe that every tail omission is at least the outer
   index, hence shifted by one. Add the outer omitted vertex. Each vertex is at
   most `b`, since `jₜ ≤ b-t+1`.
5. Equal evaluations have equal omitted sets; increasing lists with equal sets
   agree by successively removing the least element. Subtracting the offsets
   recovers every index, so the two ordered words coincide. Concatenate the first
   reduction with the reverse of the second. Length zero uses no moves; length
   one is determined by its omitted singleton. No codegeneracy or mixed move is
   introduced, and the endpoints bound every degree throughout. -/
theorem related_of_eval_eq {a b : ℕ} (hab : a ≤ b) (w v : CofaceWord a b)
    (h : w.eval = v.eval) : Related w v := by
  sorry

end SimplexCategory.CofaceWord
