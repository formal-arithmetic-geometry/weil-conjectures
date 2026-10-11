## Worker report

The module `Sheaf.LinearAlgebra.Matrix.CauchyBinet` states `Matrix.cauchy_binet`.
Its sole proof is `by sorry`; no definition or result is proved. The declaration's
source is Stacks Project, Algebra, Section 00AR, item 0F0K. The repository's copy
of `literature/stacks-project/algebra.tex` is absent on this machine, so I opened
https://stacks.math.columbia.edu/tag/0F0K directly and read the formula there.
The declaration docstring gives all five proof steps of the DAG node and names
the dependencies for the determinant expansion, repeated-column vanishing,
column permutation, and recombination.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The commutative ring is `{R : Type u} [CommRing R]`, with explicitly declared
  universe `u`. No domain, characteristic, nontriviality, or field hypothesis is added.
- The nonnegative integer dimensions are `(m n : ℕ)`; neither dimension must be positive.
- The matrices are `(A : Matrix (Fin m) (Fin n) R)` and
  `(B : Matrix (Fin n) (Fin m) R)`. The order-preserving relabeling from
  the paper's indices `1,...,k` to `Fin k` subtracts one from each index.
- The product `AB` is `A * B`. Mathlib's `Matrix.mul_apply` gives precisely
  `∑ j : Fin n, A i j * B j k`, including the empty sum.
- The subsets `S ⊆ {1,...,n}` of size `m` are the index type
  `{S : Finset (Fin n) // S.card = m}`. All finsets of `Fin n` are subsets
  of the whole index set; the subtype enforces exactly the specified cardinality.
  Its `Fintype` enumerates each subset once, without any multiplicity from permutations.
- The increasing list of indices is `S.val.orderEmbOfFin S.property : Fin m ↪o Fin n`.
  Mathlib's docstring identifies this as the increasing bijection onto the finset.
  Its range is exactly `S.val` (`Finset.range_orderEmbOfFin`).
- The selected columns are `A.submatrix id (S.val.orderEmbOfFin S.property)`;
  the selected rows are `B.submatrix (S.val.orderEmbOfFin S.property) id`.
  Both matrices have row and column type `Fin m`, and use the same increasing list.
- The local abbreviation `minors` is the finite sum of the products of these
  two determinants in `R`. It introduces no new global definition or new notion.
- The formula is the first conjunct `(A * B).det = minors`.
- The parenthetical empty-sum assertion is explicitly the second conjunct:
  `n < m → minors = 0 ∧ (A * B).det = 0`.
- The parenthetical zero-size assertion is explicitly the final conjunct:
  `m = 0 → (A * B).det = 1 ∧ minors = 1`.

Dependency declarations used, whose full signatures and docstrings were read:

- `def-weil-matrix`: Mathlib leaf `Matrix`, from
  `Mathlib.LinearAlgebra.Matrix.Defs`; it is the arbitrary-index matrix type.
- `def-weil-submatrix`: Mathlib leaf `Matrix.submatrix`, from the same module;
  its general reindexing maps are specialized directly to identity maps and
  increasing inclusions. Its recorded `mathlib_match.how` expressly allows this
  specialization, so no dependency replacement is necessary.
- `def-weil-pbc-matrix-determinant`: Mathlib leaf `Matrix.det`, from
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`; `Matrix.det_apply` gives the
  node's Leibniz convention. The main determinant import supplies the first
  two declarations transitively. Each dependency is status `mathlib`, so its
  `mathlib_match` is the record used, without requiring any `lean` record.
- Auxiliary Mathlib infrastructure: `Finset.orderEmbOfFin` from
  `Mathlib.Data.Finset.Sort`, and `Finset.fintype` / subtype finiteness from
  `Mathlib.Data.Fintype.Powerset`. These are used by the signature; no private
  copies are introduced.

Edge cases checked before writing: when `n < m` there is no cardinality-`m`
subset of `Fin n`, so the sum is empty. When `m = 0` the unique subset is empty,
its enumeration has empty domain, and every determinant in the formula has
size zero and value one. For `n = 0 < m` the product is the zero square matrix
and its determinant is zero. For `m = n = 0` the sum has exactly one term, one.
For `m = n` the only subset is all indices, reducing to determinant
multiplicativity. Rings with zero divisors and the zero ring are included;
no cancellations or divisions appear in the statement.

Searches made using `/home/ubuntu/weil-launcher/msearch.py F1
lem-weil-pbc-cauchy-binet` (logged in `searches.jsonl`):

- LeanFinder: `Cauchy Binet formula determinant of rectangular matrix product sum
  over subsets of maximal minors` returned eight hits including `Matrix.det_mul`,
  `Matrix.detp_mul`, Sylvester determinant identities, and norm lemmas. None states
  the rectangular minor sum.
- Loogle: `Matrix.det, Matrix.submatrix` returned twelve hits, including determinant
  reindexing and permutation lemmas and characteristic-polynomial sums of principal
  minors. None states Cauchy–Binet.
- Mathlib grep: `cauchy.?binet|cauchyBinet|det_mul_eq_sum`, restricted to
  `LinearAlgebra/`, returned no hits.
- LeanSearch: `Cauchy Binet formula determinant product rectangular matrices sum minors`
  was UNAVAILABLE (HTTP Internal Server Error); no verdict is inferred from that failure.
- `rg -n` in both `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `/home/ubuntu/weil-conjectures-sheaf-F1/lean/Sheaf` for matrix determinants,
  Cauchy/Binet names, and powerset sums found no statement matching this node.
  A subsequent exact search for `lem-weil-pbc-cauchy-binet|cauchyBinet|cauchy_binet`
  in both directories and `dag/lean_names_upstream.json` returned no hits.
  The direct item-id search includes the requested upstream item-id check.
- Read Mathlib `Data/Finset/Sort.lean` and `Data/Fintype/Powerset.lean` to verify
  increasing enumerations and the finite type of cardinality-`m` subsets.

No statement dispute or node fault was found. The item node copy changes only
`lean`; no new nodes or dependency modules are needed. All variables and universes
are explicit. Server compilation with `scompile.py` succeeded in 1.2 seconds,
exit code zero, with no warnings. The second reader will independently review
and deliver this statement; no second-reading section is written by the worker.

## Second reading by F1

I independently opened the item node and the delivered Lean file together, then
read all three statement-dependency nodes and their recorded Mathlib declarations.
The local Stacks TeX is absent. I read the upstream `algebra.tex` directly at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
including `section-conventions`, `section-rings-basic`, and `item-cauchy-binet`,
and checked https://stacks.math.columbia.edu/tag/0F0K and its containing section
https://stacks.math.columbia.edu/tag/00AR. The source conventions require a
commutative unital ring and explicitly allow the zero ring. No further ambient
hypothesis is imposed on this item. The node makes the shared ordering of selected
indices explicit and spells out the formula's degenerate cases faithfully.

Here is my object, hypothesis, and conclusion list, matched against the Lean:

- Ring R: `{R : Type u} [CommRing R]`. Verdict: exact, arbitrary universe,
  commutative and unital; no field, domain, nontriviality or characteristic assumption.
- Nonnegative dimensions m,n: `(m n : ℕ)`. Verdict: exact; no positivity inequality.
- An m by n matrix A and an n by m matrix B: the two binders
  `(A : Matrix (Fin m) (Fin n) R)` and `(B : Matrix (Fin n) (Fin m) R)`.
  Verdict: exact, with the order-preserving shift from one-based to zero-based indices.
  `Matrix` is the recorded declaration of `def-weil-matrix`, not a private matrix type.
- Product AB with entries summed over the middle index: `A * B`.
  Verdict: exact; I read the rectangular `HMul` instance and `Matrix.mul_apply`
  in `Mathlib/Data/Matrix/Mul.lean`, which give exactly the stated entry formula.
- Subsets S of the n indices of cardinality m:
  `{S : Finset (Fin n) // S.card = m}`. Verdict: exact; every subset occurs once.
  I read `Finset.fintype` in `Mathlib/Data/Fintype/Powerset.lean`: its enumeration
  is the powerset of the whole finite index type; the subtype keeps precisely
  the required cardinality. Equality proofs do not introduce duplicate subsets.
- Increasing order on each S: `S.val.orderEmbOfFin S.property`.
  Verdict: exact; I read its definition and docstring in `Mathlib/Data/Finset/Sort.lean`,
  as well as `range_orderEmbOfFin`. It is an increasing bijection onto S with
  domain `Fin m`; its proof argument supplies no additional hypothesis.
- Selected columns A^S and rows B_S:
  `A.submatrix id (S.val.orderEmbOfFin S.property)` and
  `B.submatrix (S.val.orderEmbOfFin S.property) id`.
  Verdict: exact; I read `Matrix.submatrix` and `submatrix_apply` in
  `Mathlib/LinearAlgebra/Matrix/Defs.lean`. The recorded dependency
  `def-weil-submatrix` allows precisely this specialization to increasing inclusions.
  The two square matrices use the identical ordering, so no sign is lost.
- Determinants of the product and both minors: `.det`.
  Verdict: exact; `def-weil-pbc-matrix-determinant` records `Matrix.det`.
  I read its `CommRing`/`Fintype`/`DecidableEq` context, definition and
  `det_apply` in `Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean`.
  The latter has the node's permutation-of-rows Leibniz convention. All finite
  and equality instances needed here are automatic for `Fin m`, not assumptions.
- Sum of products of determinants: the local `let minors : R := ∑ S : ...`.
  Verdict: exact; the factor order is det(A^S) then det(B_S), with no multiplicity.
  This is an abbreviation inside the proposition, not a new definition node.
- Main equality in R: `(A * B).det = minors`. Verdict: exact first conjunct.
- n<m, empty sum and zero determinant:
  `(n < m → minors = 0 ∧ (A * B).det = 0)`. Verdict: exact second conjunct;
  the antecedent is conditional, not an extra hypothesis on the theorem.
- m=0, both sides one: `(m = 0 → (A * B).det = 1 ∧ minors = 1)`.
  Verdict: exact third conjunct. The universal binders precede these conclusions,
  just as in the node; no subset or ordering is quantified as extra input.

Edge cases: for n<m there is no cardinality-m subset of `Fin n`, including
n=0<m. For m=0 there is exactly the empty subset and the two minors and the
product are empty square matrices, with determinant one. For m=n=0 the unique
summand is one; for m=n the unique subset is all indices, recovering the square
case. Zero A or B is covered (for m>0 the relevant determinants vanish, for m=0
empty determinants remain one). The zero ring and rings with zero divisors are
included, and characteristic two poses no restriction. `universe u` is explicit
and unrestricted. Empty schemes are irrelevant: the node has no scheme objects.

Independent searches, using different wording from the worker:

- LeanFinder via `msearch.py`: `determinant rectangular composition expansion maximal
  minors increasing injections`. Eight results include `Matrix.det_mul_aux`,
  norm-transitivity determinant lemmas, determinant block reindexing, and relations
  between deleted-row/column minors. Their displayed types do not state this formula.
- Loogle via `msearch.py`: `Matrix.det, Finset.sum, Matrix.submatrix`. Ten results
  include Laplace expansions, sums of principal minors for characteristic-polynomial
  coefficients, and deleted-row/column relations. None is Cauchy–Binet for two factors.
- LeanSearch via `msearch.py`: `rectangular matrix multiplication determinant expansion
  indexed by fixed cardinality subsets`. Service unavailable (Internal Server Error);
  this supplies no evidence of absence.
- `rg -n -i 'binet|det.*(powerset|orderEmbOfFin)|sum.*minor|minor.*sum'` on Mathlib's
  LinearAlgebra directory, upstream `WeilConjectures`, and this repository's
  `lean/Sheaf`: only principal-minor characteristic-polynomial formulas, a Bird
  determinant proof using a minor, and the scalar quadruple-product identity.
  I inspected the returned signatures from the search; they are different results.
- Exact-name/item-id searches for `cauchy_binet|cauchyBinet|lem-weil-pbc-cauchy-binet`
  in `dag/lean_names_upstream.json`, upstream `WeilConjectures`, and `lean/Sheaf`
  returned no hits. No existing declaration can replace this delivery.

No mismatch was found and no Lean or node content was changed. There are no new
nodes or dependency modules, and no statement correction requiring citer review.
The module uses only the recorded notions and the finite enumeration infrastructure.
Its sole theorem has `by sorry`; no definition contains a hole, and nothing is proved.
The source and blueprint tags occur in both docstrings. I checked the five docstring
proof steps against the node: expansion, repeated-column vanishing, image/permutation
bijection, permutation sign, and recombination, including both degenerate cases.
The namespace, header, imports and line widths meet the conventions; every variable
and universe is bound. A literal string check confirms `lean.statement` equals the
file signature verbatim and that the node differs from the repository only in `lean`.
Independent `scompile.py F1 lem-weil-pbc-cauchy-binet
lean/Sheaf/LinearAlgebra/Matrix/CauchyBinet.lean` succeeded (1.3 seconds, exit zero,
no warnings). Second reading changed only this report by adding the independent review.
