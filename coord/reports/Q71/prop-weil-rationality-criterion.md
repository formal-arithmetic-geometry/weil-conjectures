## Worker report

Existing declaration: `PowerSeries.tfae_exists_normalized_fraction`, in
`WeilConjectures.ZetaLinearAlgebra.RationalityCriterion` (upstream file lines 115–145).
The full signature and docstring were read both locally and from the current live source
using `scompile.py --source`. This delivery records that declaration with `existing: true`;
it adds no module, definition, theorem, or proof.

Hypothesis and clause matching:

- The surrounding upstream binders `{K : Type*} [Field K]` allow every field in every
  universe, and `(f : K⟦X⟧)` is the arbitrary formal power series C of the node.
- Clause 1 binds polynomials `A B : K[X]`, requires `B.coeff 0 = 1`, and asserts
  `f * (B : K⟦X⟧) = (A : K⟦X⟧)`. Rename A=P and B=Q. Since K is a field,
  multiplication of power series is commutative, so this is exactly QC=P. The
  polynomial-to-power-series coercion is the dependency's recorded inclusion.
- Clause 2 is `BddAbove (Set.range ...)` for ranks of finite square submatrices of
  `hankel f`, indexed by their size and two maps `Fin r → ℕ`. `BddAbove` here means
  existence of a natural rank bound. The recorded dependency
  `PowerSeries.hankelRank` in `Sheaf.RingTheory.PowerSeriesHankelRank` is the supremum
  of ranks indexed by increasing embeddings. Its `hankelRank_lt_top_iff` states
  exactly boundedness for those embeddings. Allowing general maps gives the same
  condition: increasing embeddings are particular maps; any finite lists of indices
  use finite sets of distinct rows and columns. Repeating indices or permuting them
  cannot increase rank, and these two finite sets can be enlarged to equal size in ℕ.
  Thus a bound for the increasing square selections also bounds every mapped square
  selection. This is precisely finite Hankel rank in the node, with no row-span or
  other substitute notion.
- Clause 3 is `∃ m d : ℕ, 1 ≤ d ∧ ∃ a : Fin d → K, ∀ n, m ≤ n → ...`.
  Naturals encode m≥0 and d≥0; `1 ≤ d` retains positive order. The equation
  `coeff (n+d) f + ∑ i, a i * coeff (n+i) f = 0` is exactly the displayed recurrence,
  with the lower terms written in increasing rather than decreasing order.
- `List.TFAE` asserts equivalence of every pair of conditions, as required.

The five statement dependencies were read in full. Mathlib leaves are `Field`
(`Mathlib.Algebra.Field.Defs`), `PowerSeries` and
`Polynomial.coeToPowerSeries.ringHom` (`Mathlib.RingTheory.PowerSeries.Basic`), and
`Polynomial` (`Mathlib.Algebra.Polynomial.Basic`). The remaining dependency is
`PowerSeries.hankelRank` / `PowerSeries.hankelRank_lt_top_iff` from
`Sheaf.RingTheory.PowerSeriesHankelRank`, which reuses upstream `PowerSeries.hankel`.
No dependency interface repair is needed.

Source checked: the original blueprint proposition and its full proof in the archived
master snapshot, plus the current main-20261015 proposition and separate proof file.
Their three conditions agree; no statement correction or dispute is needed.

Edge cases: for the zero series all three conditions hold (A=0, B=1, rank zero,
m=0, d=1, a₀=0). Constant and polynomial series admit B=1 and eventually zero
coefficients. For d=1 the sum is exactly a₀cₙ. The empty square matrix has rank zero
and is retained by both indexing conventions. Rank bounds permit R=0. No
characteristic-zero assumption, nonzero-series assumption, or universe restriction
is introduced.

Searches (also logged by msearch.py in searches.jsonl):

- LeanFinder: `formal power series rational finite Hankel rank recurrence field`:
  eight hits, including `LinearRecurrence.solSpace_rank`; no exact Mathlib criterion.
- Loogle: `PowerSeries, hankel, LinearRecurrence`: no hits; `hankel` unknown.
- LeanSearch: `rational power series equivalent finite Hankel rank eventual recurrence`:
  eight hits (LinearRecurrence solution-space rank and unrelated power-series results);
  no exact criterion.
- Mathlib grep via msearch.py: `rationality|Hankel` in Algebra/ and
  `Hankel|rationality|normalized_fraction` in RingTheory: no matches.
- Upstream rg for `def hankel|hankelRank|PowerSeries.*hankel|RationalityCriterion`
  and the exact node id found `PowerSeries.tfae_exists_normalized_fraction`.
  Its full signature and docstring state all three conditions of this node.
- Side-library rg for the node id and `tfae_exists_normalized_fraction` found no
  alternate theorem; the recorded Hankel-rank dependency supplies the named
  supremum. The final delivery therefore reuses the exact upstream theorem.

The initial draft unnecessarily restated this existing result. It has been removed
from the sandbox; the independent second reading is recorded below.

## Second reading by Q71

I independently read the node `prop-weil-rationality-criterion`, its source place in
`literature/blueprint/master/blueprint/sec-zeta-weil/sk-prop-criterion/prop-weil-rationality-criterion.md`,
the current `main-20261015` statement and proof, the dependency records, and the
upstream declaration `PowerSeries.tfae_exists_normalized_fraction` in
`WeilConjectures.ZetaLinearAlgebra.RationalityCriterion`.

The node introduces an arbitrary field `K` and an arbitrary formal power series
`C(T)=∑ cₙTⁿ ∈ K[[T]]`. The upstream theorem renders these as `{K : Type*}` with
`[Field K]` and `(f : K⟦X⟧)`; `Type*` leaves the universe unrestricted, and the
coefficient sequence is `PowerSeries.coeff n f`. Verdict: exact.

Clause (1) introduces `P,Q : K[T]`, requires `Q(0)=1`, and asserts `QC=P` in
`K[[T]]`. Lean uses `∃ A B : K[X], B.coeff 0 = 1 ∧
f * (B : K⟦X⟧) = (A : K⟦X⟧)`. The polynomial coercion is the recorded
`Polynomial.coeToPowerSeries.ringHom`; multiplication is commutative over a field,
so `f * B = A` is exactly `Q C = P`. Verdict: exact, with only harmless names and
commutative-factor order changed.

Clause (2) says the finite square submatrix ranks of the Hankel matrix
`(c_{r+s})` are bounded. Lean uses
`BddAbove (Set.range (fun x : Σ r : ℕ, (Fin r → ℕ) × (Fin r → ℕ) =>
((hankel f).submatrix x.2.1 x.2.2).rank))`. The dependency declaration
`PowerSeries.hankel` is the same matrix as the node's `PowerSeries.hankelRank`
matrix. Lean permits repeated row or column indices, while the source phrase usually
means injective finite selections; any repeated selection factors through the distinct
selected rows and columns and has no larger rank, and injective selections are included
among Lean's maps. Thus the two boundedness predicates are equivalent, including the
empty `Fin 0` square. Verdict: exact in meaning; no hypothesis or conclusion changes.

Clause (3) introduces `m≥0`, `d≥1`, coefficients `a₀,…,a_{d-1}`, and the eventual
recurrence. Lean uses `∃ m d : ℕ, 1 ≤ d ∧ ∃ a : Fin d → K,
∀ n, m ≤ n → coeff (n+d) f + ∑ i, a i * coeff (n+i) f = 0`. `Fin d` supplies
exactly the d coefficients, and its increasing index order is the displayed order
after reindexing. Verdict: exact, including `m=0` and `d=1`.

Finally, `List.TFAE` is applied to these three predicates, so all pairwise
equivalences are asserted in the same order and with no extra implication. Verdict:
exact. The source assumes no characteristic, nonzero-series, Noetherian, finiteness,
or universe restriction, and Lean assumes none.

Edge cases checked: the zero series (`A=0`, `B=1`, rank zero, `m=0,d=1,a₀=0`),
constant and polynomial series, `d=1`, the empty `Fin 0` matrix, and arbitrary field
characteristic and universe. All remain covered. No mismatch was found and no source,
statement, dependency, or Lean declaration was changed; the existing upstream theorem
is recorded verbatim as the node's declaration.

For the one-definition-per-notion check I reran `rg` over the project and upstream
trees and the recorded LeanFinder, LeanSearch, Loogle, and Mathlib searches for
rational power-series/Hankel criteria. They found only the same upstream theorem,
the canonical `PowerSeries.hankel`, and unrelated recurrence results; no competing
criterion exists. The local Hankel-rank dependency was read in full and is used only
to identify the finite-submatrix notion; no dependency repair is needed.

Fresh independent searches on second reading (2026-10-17):

- LeanFinder: `bounded ranks submatrices generating function linear recurrence`
  returned eight hits including `Matrix.eRank_submatrix_le` and
  `Matrix.rank_submatrix_le`; none states this criterion.
- Loogle: `PowerSeries, List.TFAE` returned zero hits.
- LeanSearch: `a generating series is a quotient of polynomials if and only if its
  coefficients eventually satisfy a linear recurrence` returned eight hits, mainly
  `LinearRecurrence.IsSolution` and its coefficient/solution-space API, not this theorem.
- Mathlib grep: `Hankel|normalized_fraction|rational.*recurrence` in `RingTheory`
  returned zero hits. Direct `rg` over upstream `WeilConjectures` and project
  `lean/Sheaf` recovered the theorem and the Hankel-rank dependency, and specialized
  rational-series results, with no second full criterion.

I opened the exact dependency definitions in the pinned Mathlib sources: `Field`
(`Algebra/Field/Defs.lean:180`), `PowerSeries` (`RingTheory/PowerSeries/Basic.lean:60`),
`Polynomial` (`Algebra/Polynomial/Basic.lean:74`),
`Polynomial.coeToPowerSeries.ringHom` (`RingTheory/PowerSeries/Basic.lean:836`),
`Matrix.submatrix` (`LinearAlgebra/Matrix/Defs.lean:476`), and `Matrix.rank`
(`LinearAlgebra/Matrix/Rank.lean:134`). These have precisely the objects and maps
used above. `List.TFAE` (`Data/List/TFAE.lean:29`) explicitly quantifies over every
pair of predicates in the list. `Sheaf.RingTheory.PowerSeriesHankelRank` was read
in full: it uses the same upstream matrix and a real supremum over increasing
finite index embeddings. Padding distinct row and column selections in ℕ to one
common finite size proves the bound comparison described above.

There are no new definition nodes, dependency modules, hollow definitions, new
proofs, statement corrections, or disputed statements in this delivery. Existing
upstream source is left intact; H8's new-module/proof-docstring requirements do
not call for modifying a reused upstream theorem. The node signature was compared
verbatim with both the local upstream source and `scompile.py --source` output.
