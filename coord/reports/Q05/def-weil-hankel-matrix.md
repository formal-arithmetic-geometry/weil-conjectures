## Worker report

The module `Sheaf.RingTheory.PowerSeriesHankelRank` completes the node while reusing
upstream `PowerSeries.hankel` from
`WeilConjectures.ZetaLinearAlgebra.RationalityCriterion`. The matrix declaration
already exists, but it does not separately define the ENat-valued Hankel rank;
This module supplies that missing definition without duplicating the matrix.

Both the original and current main-20261015 blueprint node were read; they have the same
matrix formula and finite-square-submatrix supremum clause.

Each hypothesis and clause is represented as follows:

* The arbitrary field is `{K : Type u} [Field K]`, with `universe u` explicit.
* The given formal power series is `(C : PowerSeries K)`.
* The infinite matrix is the imported `PowerSeries.hankel C : Matrix ℕ ℕ K`, whose
  existing body is `Matrix.of fun r s => PowerSeries.coeff (r + s) C`.
  Thus its `(r,s)` entry is exactly the coefficient `c_(r+s)`.
* `PowerSeries.hankelRank C : ℕ∞` is the `iSup` over
  `Σ k : ℕ, (Fin k ↪o ℕ) × (Fin k ↪o ℕ)` of
  `(((hankel C).submatrix x.2.1 x.2.2).rank : ℕ∞)`.
  Each order embedding lists the distinct row or column indices in increasing order;
  both lists have length `k`, so these are exactly the finite square submatrices.
* `PowerSeries.hankelRank_lt_top_iff` states the final clause verbatim in mathematical
  content: `hankelRank C < ⊤` iff there exists a natural bound `R` on every such rank.
  Its proof is `sorry`, with the complete elementary proof in its docstring: unfold
  the supremum, apply `ENat.iSup_natCast_lt_top`, and unpack boundedness of the range.
  This theorem corresponds to the final explicit assertion of this same DAG node.

Dependencies read: `def-weil-field` -> Mathlib `Field`; `def-weil-formal-power-series`
-> Mathlib `PowerSeries`; `def-weil-matrix` -> Mathlib `Matrix`;
`def-weil-submatrix` -> Mathlib `Matrix.submatrix`;
`def-weil-matrix-rank` -> Mathlib `Matrix.rank`; and
`def-weil-extended-natural-supremum` -> Mathlib `ENat` and `iSup`.

The dependency declarations and full docstrings/signatures were read in their recorded
Mathlib files: Algebra/Field/Defs, RingTheory/PowerSeries/Basic,
LinearAlgebra/Matrix/Defs and Rank, and Data/ENat/Lattice.

Edge cases checked: `r,s = 0` gives the constant coefficient; the zero series gives the
zero Hankel matrix; a nonzero constant series has only
the `(0,0)` entry nonzero, so its Hankel rank is one; the matrix
uses `ℕ`, so no finite-index or positivity assumption is imposed; and the empty
finite submatrix is represented by `Fin 0` and has rank zero.

Searches made:

* `msearch.py ... leanfinder 'Hankel matrix of a power series and supremum of ranks of finite square submatrices'`: eight hits, including `Matrix.eRank`, but no exact Hankel declaration was returned.
* `msearch.py ... loogle 'PowerSeries.hankel, Matrix.submatrix, Matrix.rank, ENat'`: zero hits (`PowerSeries.hankel` unknown to Loogle).
* `msearch.py ... grep 'hankel' LinearAlgebra/Matrix`: zero hits.
* `rg -n -i 'hankel|hankelMatrix|PowerSeries.coeff|hankel rank'` in the source and project found the exact source declaration in
  `WeilConjectures/ZetaLinearAlgebra/RationalityCriterion.lean`, lines 79--82.
* The source was read with `scompile.py --source WeilConjectures.ZetaLinearAlgebra.RationalityCriterion`;
  its docstring explicitly names `(blueprints def-weil-hankel-matrix, sk-def-roots)` and
  its body is `Matrix.of fun r s => coeff (r + s) f`.

Additional name searches with `rg -n 'hankelRank|hankel_rank|def .*submatrix.*[Rr]ank|def .*finite.*[Rr]ank'`
in the upstream project, side-project Lean, and Mathlib matrix directory found no rank
definition to reuse. The upstream sorry map confirms `PowerSeries.hankel` has neither a
local sorry nor a transitive sorry. No statement correction, dependency module, or
`STATEMENT-DISPUTED` issue was found. All new definitions have real data; the only
postponed proof is the final boundedness equivalence already asserted by this node.

Validation: `scompile.py Q05 def-weil-hankel-matrix
lean/Sheaf/RingTheory/PowerSeriesHankelRank.lean` completed cleanly in both sandbox
and library positions (1.0 s and 1.1 s). The required `deliver2.py --no-push` dry run
is also run; no delivery is pushed by this worker.

## Earlier second reading (a previous round; superseded)

Pending independent second reader. This worker has not performed or claimed an
independent second reading; the dispatcher assigns a separate reader after the
worker returns READY. The second reader must replace this handoff note with their
source-to-Lean assessment before delivery.


## Second reading by Q05

I independently read the sandbox node, its module, all six dependency nodes and
 their recorded Mathlib declarations, both master and main-20261015 blueprint
source nodes, and the slopmaster2 sketch, `49_zeta_linear_algebra.tex`, lines
571–614. This source is a blueprint definition, not a Stacks result. The sketch
assumes an arbitrary field K in the preceding definition; no characteristic,
normalization, rationality, or finiteness hypothesis is imposed on the series.
There is no repair note for this item, no statement_change, no new node, and no
dependency module in this delivery.

My source-to-Lean checklist is:

* Object K, an arbitrary field: `{K : Type u} [Field K]`, with `universe u`
  explicitly declared. Verdict: exact. Mathlib `Field` extends `CommRing` and
  `DivisionRing`; no characteristic-zero or finite-dimensionality instance is
  requested.
* Object C, an arbitrary formal series with coefficients c_n in K:
  `(C : PowerSeries K)` and `PowerSeries.coeff n C`. Verdict: exact.
  `PowerSeries` is Mathlib's univariate `MvPowerSeries Unit` abbreviation;
  `coeff` uses the single-variable multi-index, so it gives precisely c_n.
* Object H(C), an infinite matrix with rows and columns indexed by nonnegative
  integers: the imported `PowerSeries.hankel C : Matrix ℕ ℕ K`. Verdict: exact.
  I read the declaration in the local upstream source and the current source
  returned by `scompile.py --source
  WeilConjectures.ZetaLinearAlgebra.RationalityCriterion`. Its actual body is
  `Matrix.of fun r s => coeff (r + s) C`; hence every entry, including (0,0),
  is c_(r+s). Its more general semiring interface specializes to the field
  without another hypothesis or a second matrix definition.
* Finite square submatrices: the index
  `Σ k : ℕ, (Fin k ↪o ℕ) × (Fin k ↪o ℕ)` and
  `(hankel C).submatrix x.2.1 x.2.2`. Verdict: exact. Each order embedding
  enumerates a finite subset of ℕ in increasing order, and every finite
  subset of size k has exactly such an enumeration. Independent embeddings
  allow different row and column subsets. This is the increasing-indices
  convention explicitly given by `def-weil-submatrix`, rather than a
  restriction to principal or initial submatrices. The sketch permits arbitrary
  lists; repeats have zero full determinant and permutations change only its
  sign, so its rank bounds agree with this convention.
* Ranks over K: `((hankel C).submatrix r s).rank`. Verdict: exact.
  I checked `Matrix.rank`, `Matrix.rank_eq_finrank_span_row`, and the upstream
  minor characterization: on `Fin k × Fin k` the field and finite-index
  instances are available, and rank is the dimension of the row span as in
  `def-weil-matrix-rank`. There is no extra instance binder.
* Hankel rank as an extended-natural supremum: `hankelRank C : ℕ∞` is the
  `iSup` of the natural ranks cast to `ℕ∞`. Verdict: exact. The complete linear
  order in `Mathlib.Data.ENat.Lattice` supplies the least upper bound, with
  arbitrarily large finite ranks giving top.
* Finiteness iff bounded ranks: `hankelRank_lt_top_iff` states
  `hankelRank C < ⊤ ↔ ∃ R : ℕ, ∀ (k : ℕ) (r s : Fin k ↪o ℕ),
  ((hankel C).submatrix r s).rank ≤ R`. Verdict: exact. A single R precedes
  every size and both lists, so it is a uniform bound. The docstring gives the
  complete proof via `ENat.iSup_natCast_lt_top` and unpacking `BddAbove`.
  This is the final assertion of this definition node, not a new unrelated
  lemma. Its only proof is `sorry`, as stage 2 requires.

Edge cases: k = 0 is included, with the unique empty order embeddings and the
zero rank of the empty matrix. All positive sizes, including size one, are
included. C = 0 gives all ranks zero; a nonzero constant series has only entry
(0,0) nonzero and rank one. There is no assumption c_0 = 1. Series with
unbounded ranks receive top. Both positive and zero characteristic fields are
covered, and u is arbitrary; the fixed ℕ indexing does not restrict the
coefficient universe. Empty schemes and zero rings are outside the stated
field setting, rather than cases silently removed by the Lean.

Independent duplicate searches used different wording from the author's:

* LeanSearch through `msearch.py`: "Hankel rank of a formal power series
  defined by ranks of finite submatrices" returned eight hits, including
  `Matrix.rank`, `Matrix.cRank`, and unrelated power-series ideal ranks;
  none defines the requested supremum.
* LeanFinder through `msearch.py`: "extended natural rank infinite matrix
  supremum of finite minors" returned `Matrix.eRank`, `Matrix.cRank`, their
  size bounds and conversions; no supremum definition.
* Loogle through `msearch.py`: `Matrix.eRank` returned twelve declarations.
  I opened `eRank`, `cRank`, and `eRank_submatrix_le`: they use the dimension
  of the full column span and supply one inequality, not the finite-square
  supremum construction. The equivalence with column-span dimension is a
  separate mathematical result, already distinguished by the DAG's rank
  nodes. It does not provide a missing Hankel supremum declaration.
* `rg` over pinned Mathlib matrices, the upstream ZetaLinearAlgebra and matrix
  rank modules, the project's `lean/Sheaf`, and `dag/lean_names_upstream.json`
  searched `hankel`, `hankelRank`, `hankel_rank`, `HankelRank`, rank definitions,
  and combinations of supremum/iSup/submatrix/finite-square rank. The only
  exact Hankel construction is the reused `PowerSeries.hankel`. The upstream
  `Matrix.bddAbove_range_rank_submatrix_iff` is a finiteness equivalence, not
  an extended-natural rank definition. No competing `hankelRank` exists.

No mathematical or Lean mismatch was found, so I left the module and node
record unchanged. I checked that `lean.statement` is verbatim the definition's
signature from `def` to `:=`, that every variable and universe is bound, and
that the namespace, imports, 100-character lines, source/blueprint docstrings,
and real supremum data meet H5–H9. The independent LeanSearch above also fills
the missing LeanSearch category in the author's search record. The only new
content of this second reading is this report and the recorded searches.

Validation: from the sandbox directory, `scompile.py Q05
 def-weil-hankel-matrix lean/Sheaf/RingTheory/PowerSeriesHankelRank.lean` passed
both sandbox and library positions cleanly (1.1 s and 1.2 s). The required
server preflight dry run and delivery follow this reading.
