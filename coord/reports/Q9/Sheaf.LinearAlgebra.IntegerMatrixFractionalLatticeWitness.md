## What changed

Filled the proof of `Matrix.integer_fractional_lattice_witness` in
`Sheaf.LinearAlgebra.IntegerMatrixFractionalLatticeWitness`, preserving its complete signature.
The rational inverse is the explicit adjugate divided by the nonzero determinant.
The two adjugate identities give unique rational coordinates; the floor bounds and the
integer cast of matrix-vector multiplication give the nonzero integral remainder.
Updated this module's DAG proof steps to identify the Mathlib declarations used.
The final single-file compile through `lcompile.py` passed without warnings in 2.1 seconds.
A source comparison confirms that the theorem signature and all imports are unchanged.

## Proved and sorry left

Closed the one original hole: `Matrix.integer_fractional_lattice_witness`
(node `lem-trf-integer-matrix-fractional-lattice-witness`). No holes remain in the module.
Added zero holes and zero split-off statements.

## No longer needed

None. The proof uses the original adjugate-identity dependency
`lem-weil-pbc-matrix-adjugate-identity` and all original imports. No nodes or modules are pruned.
No additional Sheaf dependencies are needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The proof takes adjugates after mapping the matrix to ℚ,
rather than mapping the integer adjugate; this avoids an unnecessary cast-adjugate step.
The result also holds in rank zero (the outside-span hypothesis is impossible), so the
retained hypothesis `hr` is not mathematically necessary. Negative coordinates are covered
by the general floor inequalities, and unimodular matrices make the outside-span clause
vacuous. The unit route is unchanged.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
