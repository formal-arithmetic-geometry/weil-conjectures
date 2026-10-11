/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF lead L
-/
module

public import Mathlib.Data.Finset.Sort

/-!
# The selected upper bound of a finite subset of a directed set

Source: the blueprint of the Weil conjectures, chapter `sec-nagata-compactification`, unit
`sk-prop-nagata-sketch-approximation`, node order 328
(blueprint: def-nagata-directed-finite-upper-bound).

On a directed set `I` fix a base point `i₀`, a selected common upper bound `d i j` of every pair
and an auxiliary linear order `r` on `I`, unrelated to the order `≤` of `I`. The selected upper
bound `u F` of a finite subset `F` folds `d` over the `r`-increasing enumeration of `F`, starting
from `i₀`. The definition uses neither `≤` nor the upper-bound property of `d`; the property
`i ≤ u F` for `i ∈ F` is the separate theorem `le_directedFiniteUpperBound`.

## Main definitions

* `directedFiniteUpperBound i₀ d r F`: `d (⋯ d (d i₀ i₁) i₂ ⋯) iₙ` for the `r`-increasing
  enumeration `i₁, …, iₙ` of `F`.

## Main statements

* `directedFiniteUpperBound_empty`: the value on `∅` is `i₀`.
* `directedFiniteUpperBound_insert`: adjoining an `r`-largest new element `i` applies `d · i`.
* `le_directedFiniteUpperBound`: if `d i j` bounds `i` and `j`, then `u F` bounds `F`.
-/

@[expose] public section

universe u

/-- (blueprint: def-nagata-directed-finite-upper-bound) The *selected upper bound* of a finite
subset `F` of `I`: with a base point `i₀`, a binary operation `d` (in the source a selected
common upper bound `d i j` of `i` and `j` for the order of a directed set `I`) and an auxiliary
linear order `r` on `I`, list `F` in `r`-increasing order `i₁ ≺ ⋯ ≺ iₙ` and put
`u F = d (⋯ d (d i₀ i₁) i₂ ⋯) iₙ`, so `u ∅ = i₀` (blueprint, sec-nagata-compactification, node
order 328). The linear order `r` is explicit data, not an instance: it is unrelated to the order
`≤` of the directed set, which the definition does not use; `letI` makes `r` the order of `≤`
only inside the body. Neither directedness nor the property `i ≤ d i j`, `j ≤ d i j` is needed
to define `u`; they are the hypotheses of `le_directedFiniteUpperBound`. -/
def directedFiniteUpperBound {I : Type u} (i₀ : I) (d : I → I → I) (r : LinearOrder I)
    (F : Finset I) : I :=
  letI : LinearOrder I := r
  (F.sort (· ≤ ·)).foldl d i₀

/-- (blueprint: def-nagata-directed-finite-upper-bound) The selected upper bound of the empty
set is the base point: `u ∅ = i₀` (blueprint, sec-nagata-compactification, node order 328).
Proof: the `r`-increasing enumeration of `∅` is the empty list, and a fold over the empty list
returns its initial value `i₀`. -/
theorem directedFiniteUpperBound_empty {I : Type u} (i₀ : I) (d : I → I → I)
    (r : LinearOrder I) : directedFiniteUpperBound i₀ d r ∅ = i₀ := by
  sorry

/-- (blueprint: def-nagata-directed-finite-upper-bound) The insertion recursion:
`u (F ∪ {i}) = d (u F) i` whenever `i ∉ F` and `j ≺ i` for every `j ∈ F`, where `≺` is the
strict order of the auxiliary linear order `r` (blueprint, sec-nagata-compactification, node
order 328). Proof: since `i` is `r`-larger than every element of `F`, the `r`-increasing
enumeration of `insert i F` is that of `F` followed by `i`; a fold over `l ++ [i]` is `d` applied
to the fold over `l` and `i`. The enumeration being fixed by `r`, this recursion is well defined
although `d` need not be commutative or associative. -/
theorem directedFiniteUpperBound_insert {I : Type u} (i₀ : I) (d : I → I → I)
    (r : LinearOrder I) {F : Finset I} {i : I} (hi : i ∉ F) (hF : ∀ j ∈ F, r.lt j i) :
    directedFiniteUpperBound i₀ d r (insert i F) = d (directedFiniteUpperBound i₀ d r F) i := by
  sorry

/-- (blueprint: def-nagata-directed-finite-upper-bound)
(blueprint: lemma-nagata-directed-finite-upper-bound) The property `i ≤ u F` for `i ∈ F`,
which is not part of the definition and is proved separately (blueprint,
sec-nagata-compactification, node orders 328 and 329; it is the statement of the node
lemma-nagata-directed-finite-upper-bound): if `d i j` is a common upper bound of `i` and `j`
for every pair, then the selected upper bound `u F` of a finite subset `F` is an upper bound of
`F`. Proof: by induction on `F`, adjoining the `r`-largest element. For `F = ∅` there is nothing
to prove. Otherwise let `i` be the `r`-largest element of `F` and `F' = F \ {i}`; by
`directedFiniteUpperBound_insert`, `u F = d (u F') i`. Then `i ≤ d (u F') i`, and for `j ∈ F'`
the induction hypothesis gives `j ≤ u F' ≤ d (u F') i`; conclude by transitivity of `≤`. -/
theorem le_directedFiniteUpperBound {I : Type u} [Preorder I] (i₀ : I) (d : I → I → I)
    (hd : ∀ i j, i ≤ d i j ∧ j ≤ d i j) (r : LinearOrder I) {F : Finset I} {i : I}
    (hi : i ∈ F) : i ≤ directedFiniteUpperBound i₀ d r F := by
  sorry
