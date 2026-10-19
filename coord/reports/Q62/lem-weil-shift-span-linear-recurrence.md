## Worker report

The module `lean/Sheaf/Paper/ShiftSpanLinearRecurrence.lean` states
`exists_linearRecurrence_of_finiteDimensional_shiftSpan`, with exactly one postponed
proof (`sorry`). It constructs no new notions and changes only the item's `lean` record.
The module and declaration docstrings identify the blueprint source and give all four
steps of the node's proof, including the separate zero-dimensional case and the `d = 1`
independence case. The current main-20261015 separate file
`prop-weil-rationality-criterion.proof.md`, second paragraph, was read alongside the node;
it agrees with the recorded master source.

Hypothesis and conclusion correspondence:

- The arbitrary field is `{K : Type u} [Field K]`, with `universe u` explicitly declared.
  The sequence is the unrestricted `(c : ℕ → K)`.
- The shifted sequence `R_j` is `fun s : ℕ ↦ c (j + s)` in the conclusion.
  The existing upstream `shiftSpan K c` is exactly `V`: it is `Submodule.span K` of
  the range of all iterates of `seqShift K` on `c`. The upstream theorem
  `iterate_seqShift_apply` gives the coordinate `c (s + j)`, equal to `c (j + s)`
  by commutativity of natural-number addition. Thus the span is the node's exact span,
  not an arbitrary containing subspace.
- Finite dimensionality is `[FiniteDimensional K (shiftSpan K c)]`, the dependency's
  Mathlib finite-module predicate for this submodule's subtype.
- The requested integer order is `∃ d : ℕ`; nonnegativity is encoded by `ℕ`, and
  positivity and the dimension bound are `1 ≤ d ∧
  d ≤ max (Module.finrank K (shiftSpan K c)) 1`.
- The coefficient list of length `d` is `∃ a : Fin d → K`, without a nonvanishing
  restriction on any coefficient.
- The exact relation in the sequence space is
  `(fun s : ℕ ↦ c (d + s)) +
  (∑ i : Fin d, a i • (fun s : ℕ ↦ c ((i : ℕ) + s))) = 0`.
  The finite sum visits exactly `0, …, d - 1`; its order is immaterial in this
  commutative additive group. Addition, zero and scalar multiplication are pointwise.
- The node's equivalent recurrence from index zero is explicitly recorded by
  `(LinearRecurrence.mk d (fun i ↦ -a i)).IsSolution c`. By the read definition this
  says `∀ n, c (n + d) = ∑ i : Fin d, -a i * c (n + i)`.
  This is precisely the coordinatewise first equality after commuting natural sums
  and moving its finite sum to the other side. The two conjuncts state the two
  equivalent forms in the node, with the same order and coefficients. No eventual
  start index is introduced: all natural indices, including zero, are covered.

Dependency declarations read and used:

- `def-weil-field`: `Field`, `Mathlib.Algebra.Field.Defs`, used as `[Field K]`.
- `def-weil-sequence-subspace`: `Submodule`, `Mathlib.Algebra.Module.Submodule.Defs`;
  sequence addition and scalar multiplication are the standard Pi instances.
- `def-weil-submodule-span`: `Submodule.span`, `Mathlib.LinearAlgebra.Span.Defs`, used
  through the existing, fully constructed `shiftSpan`.
- `def-weil-finite-dimensional-subspace`: `FiniteDimensional`,
  `Mathlib.LinearAlgebra.FiniteDimensional.Defs`.
- `def-weil-vector-space-dimension`: `Module.finrank`,
  `Mathlib.LinearAlgebra.Dimension.Finrank` (the dependency's recorded module).
- `def-weil-eventual-linear-recurrence`: `LinearRecurrence.IsSolution`,
  `Mathlib.Algebra.LinearRecurrence`, with `LinearRecurrence.mk d (fun i ↦ -a i)`
  and start index zero, exactly as its `mathlib_match` specifies.
- The already existing constructions `seqShift`, `shiftSpan`, and
  `iterate_seqShift_apply` were read with their docstrings and signatures in
  `WeilConjectures.ZetaLinearAlgebra.ShiftSpan`, publicly imported here.
- Proof dependency `lem-weil-independent-family-card-le-dimension` uses
  `LinearIndependent.fintype_card_le_finrank`, whose full signature was read in
  `Mathlib.LinearAlgebra.Dimension.Finite`; that module is a non-public proof import.
  The other proof dependencies are the same definition dependencies above.

Edge cases checked before drafting:

- For the zero sequence, `V = 0`, `dim V = 0`, and the allowed choice is `d = 1`,
  `a₀ = 0`. Both the function equality and `IsSolution` then hold. The `max … 1`
  upper bound permits this case; it was not replaced by `dim V`.
- For a nonzero constant sequence, `dim V = 1`, and `d = 1`, `a₀ = -1` work.
- For `(1, 0, 0, …)`, dimension is one and `d = 1`, `a₀ = 0` work.
- For `(0, 1, 0, …)`, dimension is two and `d = 2` with both coefficients zero
  works, while order one cannot work at index zero. The statement preserves that index.
- Fibonacci sequences allow order two with coefficients `(-1, -1)`; the same
  expressions work in positive characteristic. No characteristic assumption appears.
- Universe `u` is arbitrary; no index type beyond the natural-number sequence indices
  and the finite coefficient list restricts the field universe.

Searches for an exact existing statement:

- `msearch.py … leanfinder`: query “A sequence over a field whose shifted sequences
  span a finite dimensional space satisfies a linear recurrence of positive order at
  most the maximum of its shift span dimension and one”. Eight hits included
  `LinearRecurrence`, `IsSolution`, `solSpace`, and `solSpace_rank`; no exact theorem.
- `msearch.py … loogle "LinearRecurrence.IsSolution, Module.finrank"`: zero hits.
- `msearch.py … leansearch`: query “finite dimensional span of shifts of a sequence
  implies a linear recurrence of bounded order”. Eight hits included
  `FiniteDimensional.span_finset`, `span_of_finite`, `LinearRecurrence.IsSolution`
  and `solSpace`; no bounded-order implication.
- `msearch.py … grep "shiftSpan|seqShift|IsSolution|finrank"
  Algebra/LinearRecurrence.lean`: five `IsSolution`-related hits; no shift-span theorem.
- Direct `rg` searched `WeilConjectures`, the Mathlib tree, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for shift-span, recurrence, and the proposed name;
  the exact item id was also searched in upstream. No declaration name collision or
  exact statement was found. The Mathlib search has no `shiftSpan`/`seqShift` match,
  and the side-project search had none either.
- The upstream `WeilConjectures.ZetaLinearAlgebra.ShiftSpan` file supplies `shiftSpan`
  itself; that definition is reused. Its monic-polynomial existence theorem does not
  state a positive order or its dimension bound. The full statement and proof of
  `PowerSeries.exists_forall_add_eq_zero_of_finiteDimensional_shiftSpan` in upstream
  `ZetaLinearAlgebra/RationalityCriterion.lean` were read: it gives `∃ d ≥ 1` and
  a recurrence, but no `d ≤ max (dim V) 1` bound, so it is not an exact match.

No missing notion, unusable dependency, statement correction, or statement dispute was found.

Resumed worker validation (2026-10-17): reopened every statement dependency and its
Mathlib declaration, the upstream shift constructions, both source proofs, and the prior
module. No Lean change was needed. Repeated LeanSearch, Loogle, LeanFinder and grep searches.
The refreshed LeanFinder query was “A sequence over a field whose shifted sequences span a
finite dimensional space satisfies a linear recurrence of positive order bounded by the
maximum of the dimension and one”: eight recurrence API hits, no exact bounded theorem.
The other repeated queries returned the results recorded above. The item has no maintenance
repair note. The sandbox node differs from the shared node only in `lean`.

`scompile.py Q62 lem-weil-shift-span-linear-recurrence
…/lean/Sheaf/Paper/ShiftSpanLinearRecurrence.lean` passed in both sandbox and library
forms, without diagnostics (1.0 and 1.1 seconds). Only the prescribed wrapper was used;
no source checkout or shared repository files were directly edited.

Final worker validation (2026-10-17): independently rechecked the inherited draft
against the current shared node, all six statement dependencies, the dimension-bound
proof dependency, their full Mathlib signatures, and the current blueprint proof.
The upstream recurrence theorem still lacks the required order bound; the existing
`shiftSpan` is exactly the span in the node, by `iterate_seqShift_apply` and
commutativity of addition. Repeated LeanFinder, LeanSearch, Loogle and Mathlib grep
returned the same results above. Direct searches of the full upstream source tree
and side library found no exact declaration or name collision.

The sandbox JSON differs from the current shared JSON only in `lean`; its recorded
signature equals the module signature verbatim, and every Lean line has at most
100 characters. No repair note exists for this item. No code or node correction
was needed. A fresh prescribed `scompile.py` run passed both sandbox and library
forms without diagnostics (1.3 seconds each). The independent second-reading
section is reserved for the next worker.

## Second reading by Q62

I independently opened the current shared node and the sandbox module, the six
statement-dependency nodes and their recorded Mathlib declarations, and the
independent-family dimension-bound proof dependency. I read the blueprint's
`prop-weil-rationality-criterion.md`, statement and proof, especially the second
paragraph (lines 35–41), and the corresponding current main-20261015 proof.
This source is a blueprint argument, not a Stacks lemma. Its standing assumptions
are an arbitrary field and a sequence of coefficients; there is no characteristic,
nonvanishing, or additional finiteness assumption. The explicit dimension bound
in the node follows from choosing the first dependent initial family in this
finite-dimensional span, as its four proof steps explain.

My object/hypothesis/conclusion checklist, matched to the actual signature:

1. An arbitrary field K: `{K : Type u} [Field K]`, with `universe u` explicitly
   declared. I read `Field` in `Mathlib.Algebra.Field.Defs`: it extends `CommRing`
   and `DivisionRing`, including nontriviality and inverses of nonzero elements.
   This is exactly `def-weil-field`; no field case is excluded. Verdict: exact.
2. An arbitrary sequence indexed by the nonnegative integers: `(c : ℕ → K)`.
   There is no hypothesis on its first value, its support, or eventual behavior.
   Verdict: exact.
3. For each j, the sequence R_j with s-coordinate c_(j+s): the conclusion uses
   `fun s : ℕ ↦ c (d + s)` and `fun s : ℕ ↦ c ((i : ℕ) + s)`.
   These live in the standard pointwise K-module `ℕ → K`. I read `Submodule`
   in `Mathlib.Algebra.Module.Submodule.Defs`; its zero/addition/scalar closure
   is precisely `def-weil-sequence-subspace`. Verdict: exact.
4. V is the span of all R_j, not a containing space supplied as an extra input:
   `shiftSpan K c`. I read the full definitions of upstream `seqShift` and
   `shiftSpan` and the signature/body of `iterate_seqShift_apply` in
   `WeilConjectures.ZetaLinearAlgebra.ShiftSpan`. The span is
   `Submodule.span K (Set.range fun j ↦ (⇑(seqShift K))^[j] c)`;
   the iterate's s-coordinate is `c (s + j)`, which equals `c (j + s)`.
   I also read `Submodule.span` in `Mathlib.LinearAlgebra.Span.Defs`: it is
   `sInf {p | S ⊆ p}`, exactly the dependency's intersection definition.
   Verdict: exact, and the existing construction is reused.
5. V is finite-dimensional: `[FiniteDimensional K (shiftSpan K c)]`.
   I read `FiniteDimensional` in `Mathlib.LinearAlgebra.FiniteDimensional.Defs`:
   it abbreviates `Module.Finite`, the finite-generation condition for this
   vector space. No independent ambient finite-dimensionality is assumed.
   Verdict: exact.
6. There is a positive integer order d bounded by max(dim V,1):
   `∃ d : ℕ, 1 ≤ d ∧ d ≤ max (Module.finrank K (shiftSpan K c)) 1 ∧ …`.
   Naturals encode precisely the allowable integer orders after `1 ≤ d`.
   I read the recorded `Module.finrank` in
   `Mathlib.LinearAlgebra.Dimension.Finrank`, including its finite-dimensional
   interpretation. The zero-dimensional case is retained by the `max`.
   Verdict: exact.
7. There are d arbitrary coefficients in K: `∃ a : Fin d → K`, after choosing
   d and its bounds. These represent a_0 through a_(d-1), without a nonzero
   condition or an imposed minimality condition on d. Verdict: exact.
8. The entire sequence relation is R_d plus the sum of a_i R_i equal to zero:
   `(fun s : ℕ ↦ c (d + s)) +
   (∑ i : Fin d, a i • (fun s : ℕ ↦ c ((i : ℕ) + s))) = 0`.
   Equality is in `ℕ → K`; the finite sum enumerates exactly the indices
   0 through d-1. Reversing their displayed order does not change the sum.
   The coefficient of R_d is one. Verdict: exact.
9. The equivalent recurrence holds from index zero, with these same a_i:
   `(LinearRecurrence.mk d (fun i ↦ -a i)).IsSolution c`.
   I read `LinearRecurrence` and `IsSolution` in
   `Mathlib.Algebra.LinearRecurrence`: this expands to
   `∀ n, c (n + d) = ∑ i : Fin d, -a i * c (n + i)`.
   This is the node's sign convention, including every coordinate n=0 onward.
   The second conjunct is the expressly stated equivalent form of the first,
   not an additional restriction. Verdict: exact.

I checked the docstring against all four node proof steps: D=0 and d=1;
D>0, nonzero R_0, the dimension bound and the least dependent index (including
the separate d=1 independence justification); normalization by the last nonzero
coefficient; evaluation at every coordinate. The named proof dependency's
`LinearIndependent.fintype_card_le_finrank` was opened in
`Mathlib.LinearAlgebra.Dimension.Finite`: for a finite independent family in a
finite module it bounds its cardinality by `finrank`. Its strong-rank-condition
requirement is available for every field. The non-public proof import is appropriate.

Edge cases: c=0 permits d=1 and a_0=0 even when dim V=0. A nonzero constant
sequence permits d=1 and a_0=-1. The sequences (1,0,0,…) and (0,1,0,…)
permit respectively d=1 and d=2 with zero coefficients; the latter confirms
that an eventual recurrence cannot replace the asserted recurrence at n=0.
Order zero is intentionally excluded by the source and the node; there is no
empty coefficient family to handle in a witness. The zero subspace is included;
empty schemes and unrelated index sets are not objects of this statement.
All characteristics, including characteristic two, and every field universe u
are covered. All variables and universes are explicitly bound.

Independent searches (2026-10-17), using the prescribed search wrapper:

- LeanFinder: “Finite dimensional cyclic span under sequence translation yields
  a monic relation of order no greater than its dimension, including the zero
  sequence”. Eight hits included `LinearRecurrence.solSpace_rank` and unrelated
  monic-polynomial dimension bounds; no exact statement.
- LeanSearch: “A finite dimensional vector space generated by the translates of
  a sequence gives a linear recurrence with bounded order”. Eight hits supplied
  the recurrence/solution API, not the bounded-order theorem.
- Loogle: `LinearRecurrence.IsSolution, Module.finrank`. Zero hits.
- Direct `rg` on all of upstream `WeilConjectures`, the project's `lean/Sheaf`,
  Mathlib, and `dag/lean_names_upstream.json`, using `shiftSpan`, `seqShift`,
  recurrence/dimension/finrank combinations, the proposed declaration name and
  the item id. No collision or exact theorem exists. There are no shift-span
  declarations in Mathlib or the side library. I opened the upstream related
  declarations: the monic-polynomial existence result in `ShiftSpan.lean`
  does not state a positive bounded order, and
  `PowerSeries.exists_forall_add_eq_zero_of_finiteDimensional_shiftSpan` in
  `RationalityCriterion.lean` states positive order but omits its dimension bound.
  Neither can be recorded as an exact existing match.

No mismatch was found, so I preserved the Lean and node as written and added
only this independent report. There are no new definition nodes, dependency
modules, statement changes, or maintenance repair note to audit. The module
contains one named theorem with proof `sorry`, no definitions or extra proofs,
and the required source/blueprint docstrings. Mechanical inspection confirms
that only the node's `lean` field differs from the shared node, its
`lean.statement` is verbatim the file signature, and its longest Lean line is
91 characters. Fresh `scompile.py` validation passed the sandbox and library
forms in 1.3 seconds each, without diagnostics.
