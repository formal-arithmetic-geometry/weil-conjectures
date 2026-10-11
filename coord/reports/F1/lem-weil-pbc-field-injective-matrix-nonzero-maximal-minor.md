## Worker report

The module `Sheaf.LinearAlgebra.NonzeroMaximalMinorOfInjective` states
`Matrix.exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective`. Its sole proof is
`sorry`, as required for stage 2. No definitions, extra nodes or dependency modules were
needed, and the item's node changes only in `lean`.

Hypotheses and clauses, in the order of the node:

- A field K: `{K : Type u} [Field K]`, with explicit universe `u`. No restriction on
  characteristic, finiteness, or algebraic closure.
- Nonnegative integers n and p: `{n p : ℕ}`; this includes zero.
- A p-by-n matrix with entries in K: `(B : Matrix (Fin p) (Fin n) K)`.
  `Fin r` uses indices 0 through r-1, in order-preserving correspondence with the
  node's indices 1 through r; it does not change the matrix or selection.
- Tuples K^r and coordinatewise operations: Mathlib's function type `Fin r → K`
  with its standard Pi field-module structure. `B.mulVec` has domain `Fin n → K`
  and codomain `Fin p → K` and is defined by row dot products, i.e. the finite sums
  `∑ j, B i j * v j` in the node. Linearity follows from the field operations, so
  no extra linearity hypothesis is necessary.
- Injectivity of v ↦ Bv: `(hinj : Function.Injective B.mulVec)`.
- n ≤ p: the first conclusion conjunct `n ≤ p`.
- An n-element subset of row indices with increasing enumeration: the witness
  `r : Fin n → Fin p` with `StrictMono r`. Its image is the subset S; strict
  monotonicity makes it injective, so the image has exactly n elements. Conversely
  every n-element subset of the ordered finite row set has such an enumeration.
- The submatrix on those rows and all columns: `B.submatrix r id`, of type
  `Matrix (Fin n) (Fin n) K`; its entry at x,j is `B (r x) j`.
- Nonzero determinant: `(B.submatrix r id).det ≠ 0`.
- When n=0, S is empty and the determinant is 1: the explicit conjunct
  `(n = 0 → (B.submatrix r id).det = 1)` records the determinant clause. An empty
  domain `Fin 0` makes the image of r empty automatically; no separate subset
  datum or extra assumption is needed. The clause is also supplied by Mathlib's
  `Matrix.det_isEmpty` after n=0.

Dependency declarations read and used:

- `def-weil-field`: Mathlib `Field` in `Mathlib.Algebra.Field.Defs`, extending
  `CommRing` and `DivisionRing`. This dependency is a Mathlib leaf with
  `mathlib_match: ["Field"]`, so it needs no `lean` record.
- `def-weil-matrix`: `Matrix` in `Mathlib.LinearAlgebra.Matrix.Defs`, the family
  `m → n → α`.
- `def-weil-submatrix`: `Matrix.submatrix` in the same module, taking row and column
  reindexing functions and returning entries `A (r i) (c j)`.
- `def-weil-pbc-matrix-determinant`: `Matrix.det` in
  `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`; `Matrix.det_apply` is exactly
  the node's Leibniz convention and `Matrix.det_isEmpty` gives determinant 1.

The single determinant import transitively imports the other dependencies and the
matrix-vector product. Their recorded declarations are used directly, without copies.

Edge cases checked before writing: n=0 for any p gives the unique empty selection,
vacuously strictly monotone, with empty determinant 1 and an injective map out of a
singleton. This includes p=n=0. If p=0 and n>0, the injectivity hypothesis fails:
the zero vector and a coordinate unit vector have the same image. For n>p there can
be no injective linear map over a field. When p=n, the increasing enumeration of
all rows is the identity and the conclusion is the usual nonzero determinant
criterion. The argument and signature work in every characteristic; `Field`
excludes the zero ring as the node requires.

Searches made on 2026-10-11:

- `msearch.py ... leanfinder`: "An injective rectangular matrix over a field has a
  nonzero maximal minor obtained by selecting rows in increasing order". Eight
  hits, including `Matrix.linearIndependent_rows_iff_isUnit`, total unimodularity,
  Gershgorin bounds and the Vandermonde criterion; none is this statement.
- `msearch.py ... loogle`: `Matrix.det, Matrix.submatrix`. Twelve hits for
  permutation formulas, determinant expansions and sums of principal minors;
  none asserts existence of this row selection from injectivity.
- `msearch.py ... leansearch`: "An injective rectangular matrix over a field has a
  nonzero maximal minor". Service unavailable (Internal Server Error); no verdict
  is inferred from this unsuccessful search.
- `msearch.py ... grep`, subdirectory `LinearAlgebra/Matrix`:
  `exists.*submatrix.*det|StrictMono.*det|det.*mulVec`. Nine hits, concerning
  square-matrix kernels, adjugates and nondegeneracy; no exact statement.
- `rg -n` on `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`:
  `lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor|exists_submatrix_det|StrictMono.*det|det.*mulVec`.
  The source has `Matrix.exists_submatrix_det_ne_zero_of_le_rank` in
  `WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank`; its full signature and proof
  were read. It assumes a rank bound and allows both row and column reindexing
  without monotonicity. Converting it to this statement requires a proof about
  rank, column permutations and row sorting, so it cannot be recorded as an exact
  existing statement. `UnitMaximalMinorOfDepthZero.lean` in Sheaf cites this node
  in its proof docstring and states a different theorem over a local ring.
- Exact-name `rg -n` for the chosen full declaration basename in Mathlib,
  `WeilConjectures`, `lean/Sheaf` and `dag/lean_names_upstream.json`: no collision.

Source inspection: this machine lacks `literature/stacks-project/algebra.tex`.
The cited official pages were read at
[00MY](https://stacks.math.columbia.edu/tag/00MY),
[00MW](https://stacks.math.columbia.edu/tag/00MW), and
[00MV](https://stacks.math.columbia.edu/tag/00MV). Their field specialization
supports the node; no statement correction or disputed clause was found.
The module docstring carries all four steps of the node's alternative
Cauchy--Binet proof, with the dependency IDs.

## Second reading by F1

I reread the node statement, its Stacks source tags 00MY, 00MW, and 00MV, and the
Lean declaration line by line. The correspondence is:

- The field is `{K : Type u} [Field K]`; this is exactly the node's field, with no
  characteristic, finiteness, algebraic-closure, or Noetherian hypothesis added.
- The nonnegative integers are implicit `{n p : ℕ}`; zero is included.
- The matrix is `(B : Matrix (Fin p) (Fin n) K)`, the node's `p × n` matrix over K.
- The map on tuples is `B.mulVec : (Fin n → K) → (Fin p → K)` and the hypothesis
  is exactly `Function.Injective B.mulVec`; `mulVec` supplies the node's stated
  coordinate finite-sum formula and its canonical K-linearity.
- The first conclusion clause is `n ≤ p`.
- The ordered n-element row set is represented by
  `∃ r : Fin n → Fin p, StrictMono r`; strict monotonicity is precisely the
  increasing enumeration of the selected rows.
- The selected matrix is `(B.submatrix r id)`, with all columns retained, and
  the nonzero-minor clause is `(B.submatrix r id).det ≠ 0`.
- The parenthetical zero-column convention is the explicit final clause
  `(n = 0 → (B.submatrix r id).det = 1)`.

No hypothesis or conclusion clause is missing or strengthened. The universe is
unrestricted, and the use of `Fin` covers empty index types. For `n = 0`, the
witness has empty domain and the determinant-one clause is present; for `p = 0`
and `n > 0`, injectivity is impossible; `p = n`, all characteristics, and
`n > p` are handled without extra assumptions. The zero ring is excluded by
`Field`, as in the source's field specialization.

I repeated the duplicate-definition checks with `rg` over Mathlib,
`WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`, and reviewed
the worker's LeanFinder, Loogle, LeanSearch, and grep searches. The source
repository's `Matrix.exists_submatrix_det_ne_zero_of_le_rank` has a different
rank-bound and permits arbitrary row and column maps, so it is not an exact
existing declaration. No exact declaration was found. The determinant import
provides the recorded Matrix, submatrix, and determinant notions; no private
copies or dependency modules are needed.

The only repair was editorial: this second-reading section was added to document
that the existing module and node already agree. The module was compiled with
`scompile.py` successfully; its only proof remains the required `sorry`.
