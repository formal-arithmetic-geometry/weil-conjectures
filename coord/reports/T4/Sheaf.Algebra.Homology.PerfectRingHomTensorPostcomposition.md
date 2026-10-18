## What changed

Proved `CategoryTheory.perfectRingHom_tensorDual_postcomposition` in
`Sheaf.Algebra.Homology.PerfectRingHomTensorPostcomposition`, preserving its signature.
The proof expands Mathlib's second total differential and separates the diagonal and
zero off-diagonal coordinates. On the diagonal it uses the assumed degree conditions,
tensor-comparison naturality, the sheafification adjunction, pure-tensor extensionality,
internal-Hom evaluation on the unique slice object, scalar linearity, and the integer sign
identity. All private helpers are fully proved. No definitions or existing statements changed.

Repair of the return at `6698dad9d`: removed the private `CategoryTheory.slice_unique`
helper, whose statement duplicated two existing private library helpers. Neither existing
helper is importable. The proof now uses the already imported Mathlib theorems
`CostructuredArrow.mk_surjective`, `IsDiscrete.eq_of_hom`, and `Subsingleton.elim`
directly to reduce a slice object to the identity arrow. There is no replacement
uniqueness theorem and neither existing module is modified.

Replaced the public import of `PerfectRingHomTensorDegrees` with the narrower
`PerfectRingHomTensorDegreeCondition`; added the proof-only import
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed` for naturality of the
specified tensor comparison. Removed the redundant proof imports `HomComplex` and
`PerfectRingDualTermFlat`. Updated the existing node's proof and provenance to describe
the checked argument. The public-import change is recorded in
`coord/changes/perfect-ring-hom-tensor-postcomposition-imports.md`. The unit record has no
realized statement or step assigned to this node, and the argument follows the original component-calculation route.

## Proved and sorry left

Closed one of one original holes:
`CategoryTheory.perfectRingHom_tensorDual_postcomposition`
(node `lem-pc-perfect-ring-hom-tensor-postcomposition`).

Holes added: zero. Holes remaining in the delivered module: zero. No split-offs.
The proof uses the two degree-condition hypotheses directly, not unproved existence
or invertibility results. Single-file remote compilation succeeds; the required delivery
checks additionally verify the declaration signatures, axioms, and import effects.

## No longer needed

Removed direct imports:
- `Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees` (replaced by its definition interface).
- `Sheaf.Algebra.Homology.HomComplex` (its definitions remain available through the interface).
- `Sheaf.Algebra.Homology.PerfectRingDualTermFlat` (its definitions remain available there).

This proof does not use `perfectRingHom_tensorDual_degree_exists`,
`perfectRingHom_tensorDual_degree_map_exists`, or `perfectRingHom_tensorDual_degree_isIso`.
Thus the modules `PerfectRingHomTensorDegrees`, `PerfectRingHomTensorDegreeMap`, and
`PerfectRingHomTensorDegreeIsIso`, and the latter two modules' nodes
`lem-pc-perfect-ring-hom-tensor-degree-map` and
`lem-pc-perfect-ring-hom-tensor-degree-isiso`, are unnecessary for this component calculation.
The normalizations from `lem-pc-perfect-ring-hom-tensor-degrees` are still needed as
hypotheses, as are the Hom, dual, and total-tensor definitions. The parent differential
module independently imports `PerfectRingHomTensorDegrees`, so no whole module is removed
from the targets' import closure by this delivery.

## Where the brief, the DAG or earlier work was wrong

The returned delivery unnecessarily re-proved the private slice uniqueness fact from
`PerfectRingDualTermFlat` and `RingProjectiveInternalHomExact`. The repaired proof removes
that declaration and reuses the general Mathlib API instead.

No mathematical correction was needed: the original differential calculation is valid
for arbitrary complexes, including zero modules and the zero ring, with no finiteness or
boundedness assumptions. The old public import was broader than the interface this theorem
needs. The four downstream modules retain their existing statements: the immediate consumer
`PerfectRingHomTensorDifferential` imports `PerfectRingHomTensorDegrees` itself and uses only
the unchanged postcomposition theorem from this module. No consumer adaptation is required.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
