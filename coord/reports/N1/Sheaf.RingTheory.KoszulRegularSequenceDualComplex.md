## What changed

In `Sheaf.RingTheory.KoszulRegularSequenceDualComplex`, proved
`ExteriorAlgebra.exists_koszul_quotient_augmentation` without changing its signature.
Added the proved private helper `ExteriorAlgebra.koszulBoundary_zero_formula`.
It identifies the first boundary with the linear combination of the generators.
The actual quotient map defines the augmentation. Exactness and surjectivity
identify its degree-zero homology map with a cokernel isomorphism; regularity
handles positive degrees. Extension by zero gives the required integer-indexed
augmentation and its evaluation formula. No arbitrary object is chosen from an
unproved existence theorem. Updated the existing node's proof with this argument.

The module compiles cleanly with lcompile.py. No imports were added. The proof
covers an empty sequence, the zero ring, and the unit ideal: no nontriviality or
proper-ideal hypothesis is used. The augmentation remains relative to the
existing Koszul construction, whose underlying dependencies may still use sorry.

## Proved and sorry left

Closed 1 of the 4 original holes:
`ExteriorAlgebra.exists_koszul_quotient_augmentation`.
Added 0 holes; this is a complete proof of the augmentation clause, not a
new decomposition. The following three declarations remain exactly `by sorry`,
all attached to `lem-sc-koszul-regular-sequence-dual-complex`:

- `ExteriorAlgebra.exists_unique_koszul_conormal_comparison`.
- `ExteriorAlgebra.exists_intrinsic_koszul_ext_determinant`.
- `ExteriorAlgebra.koszul_conormal_comparison_localization`.

The previously proved cohomology and change-of-generators clauses are untouched.

## No longer needed

None. No original imports were removed. No dependency nodes or modules are
pruned: the three remaining clauses still need the original duality route.
The quotient augmentation itself needs only the Koszul complex and regularity,
plus Mathlib's cokernel, single-complex, and extension APIs, available through
the retained imports. Three trial Mathlib imports were redundant and were
removed before the final compile; they were never part of the original module.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The DAG's degree-zero quotient calculation is
sufficient for the augmentation clause and has now been written in Lean.
The original file had four holes; cohomology and change of generators were
already proved. Searches through LeanFinder, Loogle, and grep found no existing
Koszul quotient augmentation theorem. Mathlib supplies the general cokernel
and quasi-isomorphism APIs used here. No unit-level route was bypassed.

## Second reading by N1

I checked the delivered module against the repository version line by line. Existing declaration signatures and visibility are unchanged; the only proof change is the augmentation theorem and its private helper. The module compiles cleanly with `lcompile.py`, and the proof introduces no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the remaining three `sorry` declarations are the named open clauses listed above. The augmentation statement is unchanged and its construction uses the quotient map determined by the ideal, so no arbitrary witness is selected. The proof follows the unit route through the Koszul complex, regularity, degree-zero cokernel, and extension by zero. No imports or dependencies can be pruned, and no new statement or node was added.
