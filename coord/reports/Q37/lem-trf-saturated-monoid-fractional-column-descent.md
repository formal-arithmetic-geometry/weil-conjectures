## Worker report

The module `Sheaf.LinearAlgebra.SaturatedMonoidFractionalColumnDescent` states
`AddSubmonoid.saturated_fractional_column_descent`. Its sole theorem has proof
`sorry`, with the complete five-step DAG proof in its docstring. No definitions,
new nodes, dependency repairs, or statement corrections are needed. Only the
item's `lean` field changes.

Hypothesis and conclusion correspondence:

- The positive rank is `{r : ℕ} (hr : 1 ≤ r)`; `Fin r → ℤ` is the full integer
  lattice of rank `r`, with no restriction to a generated subgroup.
- `S : AddSubmonoid (Fin r → ℤ)` includes exactly zero membership and closure
  under addition. `hS : S.NSMulSaturated` means that `n • t ∈ S` implies
  `n = 0 ∨ t ∈ S`, equivalently the node's implication for every positive natural
  `n`. In particular this is saturation in the ambient lattice, as required.
- `A : Matrix (Fin r) (Fin r) ℤ` is the integer square matrix;
  `hcols : ∀ i, (fun k ↦ A k i) ∈ S` specifies its columns, not its rows.
  `hdet : A.det ≠ 0` is the required nonsingularity.
- `a : Fin r → ℚ` and `ha : ∀ i, 0 ≤ a i ∧ a i < 1` give both coefficient bounds.
- `x : Fin r → ℤ` together with
  `hx : ∀ k, (x k : ℚ) = ∑ i, a i * (A k i : ℚ)` says exactly that the stated
  rational combination is integral, naming its integer vector. There is no
  stronger divisibility or representation assumption.
- The first conjunct is `x ∈ S`. The remaining conjunction quantifies over
  every `j : Fin r` with `0 < a j`.
- The matrix in each conclusion is the canonical integer matrix `A.updateCol j x`.
  `∀ i, (fun k ↦ (A.updateCol j x) k i) ∈ S` gives all its columns in `S`.
- The next conjunct is `((A.updateCol j x).det : ℚ) = a j * (A.det : ℚ)`.
  The following three conjuncts give, respectively, strict positivity of the
  new absolute determinant, equality to `a j * abs (A.det : ℚ)`, and strict descent
  below `abs (A.det : ℚ)`. Every determinant in these clauses is explicitly cast
  from the integer determinant into the rationals.

Dependencies and interfaces read:

- `def-weil-pbc-matrix-determinant` records `Matrix.det` from
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`, publicly imported. Its full
  signature is a square matrix over a commutative ring, indexed by a finite
  decidable type, returning an element of that ring. Its docstring gives the
  Leibniz definition and `Matrix.det_apply` gives the column-indexed formula.
- The proof dependency `lem-weil-pbc-det-repeated-column-zero` matches
  `Matrix.det_zero_of_column_eq` in the same module, already imported. It takes
  distinct column indices and equality of their entries at every row, and
  concludes determinant zero. There is no additional project proof module to import.
- Root saturation is the existing `AddSubmonoid.NSMulSaturated`, generated in
  `Mathlib.GroupTheory.Subgroup.Saturated`, publicly imported; its defining
  docstring and the generating declaration `Submonoid.PowSaturated` were read.
- `Matrix.updateCol` from `Mathlib.LinearAlgebra.Matrix.RowCol` (exposed by the
  determinant import) is actual column replacement by `Function.update`.
- `Mathlib.Algebra.Order.Field.Rat` supplies the ordered rational field used
  for the coefficients, casts, absolute values and inequalities.

Sources read: the Stacks source `literature/stacks-project/algebra.tex`,
`item-cauchy-binet`, lines 282–288; the text of ILO VIII 3.1.17, printed page 101,
from the locally supplied PDF via `pdftotext`. The former provides determinant
context; the latter defines saturation in groupification. The node explicitly
assumes the stronger ambient-lattice saturation, and its argument is agent-supplied.
No claim that either source states this entire theorem is made.

Edge cases checked mathematically before writing:

- Rank zero is expressly excluded by `hr`, exactly as in the node.
- If all coefficients vanish, `hx` gives `x = 0`, hence `x ∈ S`; the conditional
  assertions for positive coefficients are vacuous. No positive-coefficient
  existence assumption was added.
- For rank one with `A = [2]`, `S` the nonnegative integers and `a = [1/2]`, the
  integral vector is `[1]` and the absolute determinant drops from 2 to 1.
- Negative determinants are permitted: rank one `A = [-2]`, `S = ⊤` and the
  same coefficient give `x = [-1]`, with the signed determinant identity and
  positive absolute-value descent both valid.
- `a j = 0` imposes no replacement conclusion; `a j = 1` is excluded exactly
  by the strict upper bound. Determinant `±1` permits no eligible positive
  coefficient yielding an integral replacement; this follows from the
  assumptions and is not an added hypothesis.
- `S = ⊥` cannot contain a nonsingular matrix's columns for positive rank;
  `S = ⊤` is allowed. No finiteness, sharpness or spanning hypothesis on `S`
  was added.

Searches made using the prescribed `msearch.py Q37 <item>` wrapper:

- LeanFinder: “An integral rational nonnegative combination of columns in a root
  saturated additive submonoid belongs to the monoid and fractional column
  replacement strictly lowers the absolute determinant”. Eight hits, mostly
  `FixedDetMatrices` reduction for 2-by-2 matrices; none is this statement.
- Loogle: `Matrix.det_updateCol_sum`. One exact hit for the determinant identity
  alone. Its signature and source docstring were read; it does not provide
  saturated monoid membership or strict inequalities.
- Mathlib grep: `det_updateCol|NSMulSaturated|fractional.*[Cc]olumn`. Eighteen
  hits, including determinant identities and the existing saturation notion;
  none states the complete theorem.
- LeanSearch: “root saturated additive submonoid integral rational nonnegative
  linear combination belongs to the monoid”. Eight hits for additive submonoids,
  nonnegative submonoids and saturation; no full theorem.
- `rg` in `lean/WeilConjectures` and `dag/lean_names_upstream.json` for
  `saturated_fractional_column_descent|fractional.*[Cc]olumn|NSMulSaturated|det_updateCol_sum`:
  no matches. `grep -rn` for this item's id in `lean/WeilConjectures`: no matches.
- `rg` in `lean/Sheaf` for `saturated_fractional_column_descent|det_updateCol_sum|NSMulSaturated`:
  only `FaceSubgroupSaturated.lean` uses the existing saturation predicate in a
  different theorem about faces; no duplicate of this statement.

No statement dispute or node fault found.

## Second reading by Q37

The dispatcher explicitly prohibits starting other agents. This section records
a second self-reading with the original JSON and the completed Lean file open;
the maintainer supplies the independent delivery review.

Rechecked each hypothesis and clause against the correspondence above: the
matrix has integer entries; its columns, the rational combination and the
replacement column all use the same row and column order. The natural-scalar
saturation predicate quantifies over every ambient integer vector, with its
zero-scalar disjunction equivalent to the stated positive-scalar implication.
The named integral `x` and its coordinatewise cast equality express the original
integrality premise without a chosen preimage. The conclusions retain all
columns, the signed identity, the absolute-value identity, strict positivity
and strict descent. The conditional quantifier keeps the all-zero-coefficient
case. No mismatch or correction was found.

Validation: the initial server compile passed without warnings. The first dry
run parsed a top-level absolute-value bar as a declaration boundary; the file
and verbatim node signature now spell absolute values as `abs`, with identical
mathematical meaning. All checks are rerun on this syntax.
