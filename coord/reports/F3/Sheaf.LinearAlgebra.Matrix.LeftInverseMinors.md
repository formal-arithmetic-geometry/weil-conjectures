## What changed

Proved `Matrix.scalar_left_inverse_maximal_minors` in
`Sheaf.LinearAlgebra.Matrix.LeftInverseMinors`, preserving its signature and visibility.
Added the proof-only import `Mathlib.LinearAlgebra.Matrix.Adjugate`.
The projection is a row submatrix of the identity; `Matrix.one_submatrix_mul`
and `Matrix.adjugate_mul` provide a scalar left inverse for each generator.
`Submodule.span_induction` extends this construction to the ideal without choosing
coefficients. Taking determinants and applying the existing `Matrix.cauchy_binet`
proves both the explicit formula and ideal membership.
Updated the node's first two proof steps and proof-origin place to record this
implementation of the same argument. All proof dependencies are retained.
The unit route is unchanged; this node realizes no unit-level step itself.

Source checked: [Stacks 07DQ](https://stacks.math.columbia.edu/tag/07DQ),
`lemma-matrix-left-inverse`, including the projection/adjugate construction and
Cauchy–Binet conclusion. The local literature TeX is absent, so the source was
read on the official Stacks site.

## Proved and sorry left

Closed the sole hole `Matrix.scalar_left_inverse_maximal_minors`
(node `lem-weil-pbc-matrix-left-inverse-minors`). No holes added; no sorry remains
in the delivered module. This is a proof from the existing planned dependency,
not a decomposition into new holes. `Matrix.cauchy_binet`
(node `lem-weil-pbc-cauchy-binet`, module `Sheaf.LinearAlgebra.Matrix.CauchyBinet`)
remains an existing imported sorry and is not changed by this delivery.
The adjugate and ideal-induction portions use proved Mathlib lemmas.
The proof is uniform for zero columns, zero rows where allowed, and the zero ring;
no positivity or nontriviality assumption is introduced.

## No longer needed

None. No imports were removed, and all four planned proof dependencies are used:
`def-weil-matrix`, `def-weil-submatrix`, `lem-weil-pbc-matrix-adjugate-identity`,
and `lem-weil-pbc-cauchy-binet`. No node or module is pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface error found. The original module lacked the
proof-only adjugate import needed for its planned construction; it is now added.
The finite coefficient expansion can be implemented directly by ideal-span
induction, with no extra theorem or choice of coefficients.


## Second reading by F3

1. **Interface unchanged — pass.** Compared the entire delivered Lean module and
   node with the repository versions using `diff -u`. The sole existing declaration,
   `Matrix.scalar_left_inverse_maximal_minors`, has a byte-for-byte identical signature
   (also checked by extracting the declaration text before `:= by`). Its visibility,
   hypotheses, conclusion, and all definitions are unchanged. The only Lean changes
   are the proof body and a plain, proof-only adjugate import. No change record is needed.
2. **Proof and axioms — pass.** Independently compiled the delivered file with
   `lcompile.py`: no errors or warnings. Read every witness and induction branch:
   the row projection gives the selected minor, the adjugate proves the generator
   case, and zero/addition/scalar multiplication establish the ideal-span closure.
   Taking determinants and the existing Cauchy–Binet formula gives exactly the
   displayed coefficients; `Ideal.mul_mem_left` and `Ideal.subset_span` prove membership.
   No sorry, forbidden declaration, hollow definition, or arbitrary data definition
   occurs in this file. A scratch copy with `#print axioms` for both the delivered
   theorem and `Matrix.cauchy_binet` compiled: both show only `propext`,
   `Classical.choice`, `Quot.sound`, and the existing imported `sorryAx`.
3. **Split-off statements and edge cases — pass.** No statements, nodes, or holes
   were added, so no split-off obligation needs repair. Checked `m = 0` (the empty
   determinant is one and the ideal is the whole ring), `n = m = 0`, `m = n`,
   and the zero ring. The proof requires no nontriviality, positivity, or added
   hypothesis. Its existential witnesses occur only in proposition proofs, never
   in data definitions.
4. **Shortest route, imports, and unit — pass.** Searched the local Sheaf library
   and Mathlib's linear algebra/ring theory sources for Cauchy–Binet, ideals of
   minors, and scalar left inverses; no shorter applicable theorem was found.
   Also ran the launcher's Mathlib grep search with different keywords. The existing
   planned `Matrix.cauchy_binet` is used directly, and the adjugate identity is
   the proved Mathlib declaration attached to its dependency node. The four public
   imports supply the determinant, sorted enumeration, finite subset indexing,
   and ideal span in the statement; both plain imports serve only the proof.
   No unused proof dependency or removable module was found. Read
   `dag/units/sk-thm-p1.json`: this auxiliary node is absent from its `realized`
   statement and steps, and none of that unit's route is bypassed or changed.
   `## No longer needed` is complete.
5. **DAG and source — pass.** The node's four proof steps agree with the Lean;
   its `proof_deps` is exactly the union of the steps' named uses. The adjugate
   dependency maps to Mathlib `Matrix.adjugate_mul`; the other mathematical
   dependency maps to the imported `Matrix.cauchy_binet`. Only `proof` and
   `proof_origin` changed in the node. Independently read the official Stacks
   07DQ statement and proof: the projection/adjugate construction and determinant
   combination are the same argument. No new node fields are required.

Second reading changed only this report by adding the independent checks and
verdicts above; the Lean proof and node changes were correct as delivered.
