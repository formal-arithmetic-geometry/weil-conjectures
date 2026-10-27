## Worker report

The module `Sheaf.RingTheory.LocalIrredundantRelationMatrix` states
`IsLocalRing.irredundant_relation_matrix`, with `sorry` as its only proof. It introduces
no definitions or helper theorems. Only the item's `lean` field changes; the accepted
Q75 stage-1 split is preserved. The current queue lists this node at stage 2, and the
stage handoff in coord/brief-stage2.md §0 explicitly permits stating a reviewed split.
No repair note for this item is present in the read repository.

Source read: literature/stacks-project/algebra.tex, Tag 0592,
`lemma-projective-freeness-criteria`, including the proof's irredundancy argument and
its final paragraph (lines 20672–20680). The finite tuple and the column relation in
that paragraph are precisely those of the DAG statement. No statement correction is
needed, and there is no statement dispute.

The hypotheses and clauses match as follows:

- A commutative local ring is `{R : Type u} [CommRing R] [IsLocalRing R]`.
  Mathlib's local ring is nontrivial and has exactly one maximal ideal, named
  `IsLocalRing.maximalIdeal R`; `maximal_ideal_unique` and `eq_maximalIdeal` in
  Mathlib/RingTheory/LocalRing/MaximalIdeal/Basic.lean identify this with the node's
  unique maximal ideal. No additional ring property or characteristic is assumed.
- The arbitrary nonnegative integer is `(n : ℕ)`, and the tuple is `(a : Fin n → R)`.
  Reindexing 1,...,n by 0,...,n-1 changes no algebraic condition.
- Irredundancy is `hirr : ∀ j : Fin n, ¬ ∃ c : Fin n → R,
  a j = ∑ i ∈ Finset.univ.erase j, a i * c i`.
  The erased finite sum contains exactly the indices different from j. Quantifying
  coefficients on all indices is equivalent to quantifying them on the erased set:
  the unused value at j is arbitrary, and a family on that set extends by zero.
- The square matrix is `(B : Matrix (Fin n) (Fin n) R)`.
- Every column relation is `hrel : ∀ j : Fin n,
  a j = ∑ i : Fin n, a i * B i j`. The factors and the row/column convention agree
  exactly with the source; no transpose or linear-independence hypothesis is used.
- The first conclusion is `∀ j : Fin n,
  1 - B j j ∈ maximalIdeal R ∧ IsUnit (B j j)`, recording BOTH diagonal assertions.
- The next conclusion is `∀ i j : Fin n, i ≠ j → B i j ∈ maximalIdeal R`.
- The determinant assertion is `IsUnit B.det`.
- Invertibility is the explicit two-sided condition
  `∃ V : Matrix (Fin n) (Fin n) R, B * V = 1 ∧ V * B = 1`.
  Matrix multiplication and matrix one are Mathlib's usual operations.
- The node's meaning of a unit, `∃ v, u * v = 1`, agrees with Mathlib `IsUnit` in a
  commutative ring, by `isUnit_iff_exists_inv` (Units/Defs.lean, lines 436–438).
  Hence the bundled formulation does not strengthen the unit clauses.

Dependency declarations read and used:

- def-weil-matrix: `Matrix`, Mathlib.LinearAlgebra.Matrix.Defs, definition and
  docstring at lines 58–63. Imported publicly and used as the matrix carrier.
- def-weil-pbc-matrix-determinant: `Matrix.det`,
  Mathlib.LinearAlgebra.Matrix.Determinant.Basic, lines 49–69, including the full
  signature, commutative-ring context and `Matrix.det_apply` Leibniz formula.
  Imported publicly and used as `B.det`.
- Proof dependency lem-weil-pbc-local-ring-unit-criterion:
  `IsLocalRing.notMem_maximalIdeal`, from its mathlib_match, in
  Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic, lines 79–84. The public import
  also provides the maximal ideal used in the statement.
- Proof dependency lem-weil-pbc-matrix-adjugate-identity:
  `Matrix.mul_adjugate` and `Matrix.adjugate_mul`, from its mathlib_match, in
  Mathlib.LinearAlgebra.Matrix.Adjugate, lines 264–273. Imported as a proof import.
  I also read `adjugate_fin_zero` and `adjugate_fin_succ_eq_det_submatrix` at
  lines 360–371 to check the empty and cofactor conventions. The theorem's
  docstring records all four accepted proof steps and their DAG dependencies.

Edge cases checked before writing:

- n = 0: the tuple, irredundancy, relation and entry conclusions are vacuous;
  determinant is the empty product 1 and both inverse equations hold for the
  unique empty matrix. No nonempty-index assumption is present.
- n = 1: irredundancy says a(0) is nonzero (the other-entry sum is empty), but
  does not say a(0) is regular. The relation only implies
  `(1 - B 0 0) * a 0 = 0`, which is the intended hypothesis.
- Zero divisors: in k[ε]/(ε²), a = (ε) and B = (1+ε) satisfy the assumptions.
  This confirms that B = 1 must not be asserted and cancellation must not be used.
- Over a field, irredundant tuples have length at most one. For length one the
  relation forces B = 1; for length zero the empty case applies.
- A tuple containing a zero entry fails irredundancy, as it should. The zero ring
  is excluded by unique-maximal-ideal localness itself, equivalently by Mathlib's
  IsLocalRing, not by an extra assumption. The ring universe u is unrestricted.

Searches actually run with msearch.py Q83 lem-trf-local-irredundant-relation-matrix:

- LeanFinder: "A matrix fixing an irredundant finite tuple in a commutative local
  ring has unit diagonal entries, off-diagonal entries in the maximal ideal, and
  unit determinant". Eight hits: matrix transvection inductions, triangular
  SL/GL facts and FixedDetMatrices.reps_one_id. They concern fields, integer
  matrices or determinant-preserving operations; none states this result.
- Loogle: `IsLocalRing, Matrix, IsUnit`. Successful search, zero hits.
- Mathlib grep: `irredundant|[Mm]inimal.*[Gg]enerat|[Rr]elation.*[Mm]atrix` in
  RingTheory/LocalRing. One hit, Etale.lean:18, about a minimal polynomial;
  no matching tuple-relation result.
- LeanSearch: "In a local ring, a matrix fixing a minimal generating tuple is
  congruent to the identity modulo the maximal ideal and invertible". Eight hits:
  notMem_maximalIdeal, mem_maximalIdeal, a Krull-dimension-zero nilpotence criterion,
  Matrix.invertibleEquivDetInvertible, Matrix.isUnit_iff_isUnit_det, RingCon.matrix,
  RingCon.matrix_ofMatrix and LinearMap.isUnit_toMatrix_iff. These provide the local
  unit criterion or general invertibility criteria, not the irredundancy deduction.
- rg in lean/WeilConjectures and lean/Sheaf:
  `irredundant|local.*relation.*matrix|relation.*matrix.*local`. Only unrelated
  topological irredundant families, valuations and minimal generators appeared.
- grep -rn of the exact item id in lean/WeilConjectures: no hits.
- rg of `irredundant_relation_matrix` in Mathlib, lean/WeilConjectures,
  lean/Sheaf and dag/lean_names_upstream.json: no hits, so the declaration is new.

Validation: scompile.py compiled this file both under its sandbox name and its
actual library module name cleanly (0.9 s and 1.0 s). All universes and binders are
explicit. There are no diagnostic commands, file-local definitions or instances,
new DAG nodes, dependency repairs, or changes to the accepted mathematical statement.
The maintainer performs the independent delivery review as specified in this brief.

## Second reading by Q83

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
