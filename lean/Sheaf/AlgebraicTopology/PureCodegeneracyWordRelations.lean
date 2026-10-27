module

public import Sheaf.AlgebraicTopology.PureCodegeneracyWord

/-!
# Completeness of the pure codegeneracy relations

Source: Stacks, simplicial.tex, Tags 0167(5) and 0168, omitted pure-codegeneracy
normal-form input, with the proof supplied in the DAG
(blueprint: lem-sfb-pure-codegeneracy-word-relations).
-/

@[expose] public section

set_option autoImplicit false

namespace SimplexCategory.CodegeneracyWord

/-- Equal-valued raw codegeneracy words are connected using only adjacent
codegeneracy relations, in either direction, within their endpoint degrees.

Source: Stacks, Tags 0167(5), 0168, omitted pure-codegeneracy input; the following
proof is supplied by the DAG (blueprint: lem-sfb-pure-codegeneracy-word-relations).

Proof:
1. A word from degree `a` to degree `b` has `k = a - b` letters, since each
   codegeneracy lowers degree by one. List its indices in outermost-first order
   as `u₀,...,uₖ₋₁`, where `uₚ ≤ b + p`. The sole word for `k = 0` is empty.
   The ordinal category is that of def-weil-pbc-simplicial-set; its generator
   `σ_i` sends `x` to `x - 1` for `x > i`, and to `x` otherwise.
2. Replace an adjacent pair `(j,i)` with `i ≤ j` by `(i,j+1)`. This is typed
   because `j ≤ r`, hence `i ≤ r` and `j+1 ≤ r+1`. Both composites send `x`
   to `x - 1_{x>i} - 1_{x>j+1}`. For the left composite the outer subtraction
   occurs iff `x - 1_{x>i} > j`, equivalently `x > j+1`; for the right one it
   occurs iff `x - 1_{x>j+1} > i`, equivalently `x > i`. Evaluation is preserved
   after adding unchanged surrounding factors as well.
3. The nonnegative deficit `D = sum (b+p-uₚ)` decreases exactly by one with
   each such move. Induct on `D`: a non-increasing adjacent pair permits a
   move followed by induction; otherwise the indices are strictly increasing.
   At `D = 0` every index is `b+p`. This yields a finite reduction to an
   increasing word without changing its value or its degree sequence.
4. For an increasing word with index set `T`, induction on `k` gives
   `q(x) = x - #{t ∈ T | t < x}`. Remove its rightmost factor, whose index is
   the largest `t`. For `x ≤ t` that factor fixes `x` and `t` is not counted.
   For `x > t` it sends `x` to `x-1 ≥ t`; all other indices are smaller than
   `t`, so induction gives `(x-1)-(k-1) = x-k`. The empty word is the identity.
5. For `x < a`, consecutive values differ by `1 - 1_{x∈T}`. Thus `T` is
   exactly the set of `x < a` with `q(x) = q(x+1)`. Equal evaluations determine
   equal index sets and hence equal increasing lists, by successively taking
   the least remaining element; the two typed increasing words coincide.
6. Reduce each original word, identify the increasing words using their equal
   values, and concatenate the first path with the reverse of the second.
   All factor degrees stay `b,...,a-1` in outermost-first order, so every
   ordinal degree stays between `b` and `a`. Every move uses only the displayed
   codegeneracy relation in an unchanged context. For `a = b` both paths are
   empty. No coface or mixed relation occurs. -/
theorem related_of_eval_eq {a b : ℕ} (hba : b ≤ a) (w v : CodegeneracyWord a b)
    (h : w.eval = v.eval) : Related w v := by
  sorry

end SimplexCategory.CodegeneracyWord
