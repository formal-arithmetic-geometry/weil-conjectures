## What changed

Proved `Matrix.exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective` in
`Sheaf.LinearAlgebra.NonzeroMaximalMinorOfInjective`, with its signature unchanged.
Added proof-only imports of `Mathlib.LinearAlgebra.Basis.VectorSpace` and
`Mathlib.LinearAlgebra.Matrix.ToLin`. The existing proof-only Cauchy–Binet import stays.

The proof follows all four existing DAG steps. Apply
`LinearMap.exists_leftInverse_of_injective` to `B.toLin'`, convert its retraction to
a matrix by `LinearMap.toMatrix'`, and use compatibility with composition to obtain
`C * B = 1`. Cauchy–Binet implies that some increasingly enumerated row minor is
nonzero: otherwise its sum would vanish, contradicting `1 ≠ 0`. The selected
finite set's cardinality gives `n ≤ p`; the empty determinant gives the zero-column
clause. The existing node and docstring describe precisely this route and need no change.

## Proved and sorry left

Closed one hole:
`Matrix.exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective`
(node `lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor`).

No holes remain in the item, and no holes or declarations were added elsewhere.
This is a proof, not a decomposition. The existing Cauchy–Binet dependency is itself
proved in the current library source. Edge cases are included without additional
hypotheses: `n = 0` uses the empty determinant, and if `p < n`, the contradiction
argument precludes an injective matrix.

## No longer needed

None. No imports were removed, and every existing proof dependency remains used.
The source-library rank/minor candidate was examined but is not needed: it would
require additional reordering of its row and column selections, whereas the
planned Cauchy–Binet route directly produces the required increasing rows.
No unit statement or proof step was bypassed.

## Where the brief, the DAG or earlier work was wrong

None. The DAG plan fits the existing Lean interfaces. The Cauchy–Binet declaration
is already proved, so the complete proof introduces no unresolved dependency.

## Second reading by Q4

1. **Interface unchanged — pass.** Compared the complete sandbox module with the
   repository using `diff -u`. The existing declaration's signature, visibility,
   universes, docstring and public import are byte-for-byte unchanged. Only its
   proof and two proof-only imports differ; no change record is needed.
2. **Kernel proof — pass.** Compiled the delivered module with `lcompile.py`, with
   no errors or warnings. A scratch copy with `#print axioms
   Matrix.exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective` reports
   exactly `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
   There are no remaining holes, definitions, new declarations, or forbidden
   mechanisms in the delivery. The retraction is used inside a theorem proof,
   and is supplied by a proved Mathlib theorem, not unproved existence data.
3. **Split statements and edge cases — pass.** No statements were split off.
   Checked the empty-column case (empty determinant equals one), the zero-row
   case, and `p < n` (the finite-sum contradiction rules out injectivity).
   For positive square size the selected rows enumerate the entire row set.
4. **Route and imports — pass.** Read the upstream
   `Matrix.exists_submatrix_det_ne_zero_of_le_rank`: using it would additionally
   require rank calculations and row/column reordering. A fresh Loogle search
   for `Matrix.det, StrictMono` returned no direct replacement. The existing
   Cauchy–Binet route gives increasing rows directly. Scratch compilations
   removing each added import separately fail respectively at
   `LinearMap.exists_leftInverse_of_injective` and `Matrix.toLin'`, confirming
   both imports are needed. Cauchy–Binet is used explicitly. No old dependency
   is pruned. Read `dag/units/sk-thm-p1.json`: no realized unit node or unit
   proof step is bypassed or changed.
5. **DAG matches proof — pass.** Read the item's node and the Mathlib retraction
   leaf. Its four proof steps agree with the Lean: linear retraction, coordinate
   matrix left inverse, Cauchy–Binet, and a nonzero summand/cardinality argument.
   The existing `proof_deps` and agent-written `proof_origin` remain accurate;
   no new node or node edit is necessary.

Second reading changed only this report, adding the independent checks and their
results. The Lean proof and metadata needed no repair. Closed one existing hole
and added zero holes, with no decomposition.
