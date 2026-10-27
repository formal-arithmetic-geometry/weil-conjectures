## What changed

Proved `AlgebraicGeometry.strictTransform_affine_torsion_comparison` in
`Sheaf.TraceFormula.StrictTransformAffineTorsionComparison` without changing its signature.
Added the private proof import `Mathlib.RingTheory.Flat.Localization`.
The proof realizes the chart inclusion as a module localization, tensors it with M,
and uses preservation of regular scalar multiplication by localization to identify
both torsion submodules with the kernel of the same localization map.
Updated the theorem docstring and its existing DAG node to describe this implementation
of the Tag 080H localization argument. No definitions or public interfaces changed.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.strictTransform_affine_torsion_comparison`
(node `lem-trf-strict-transform-affine-torsion-comparison`).
Zero holes remain in the item. Zero holes added; zero statements split off.
The proof uses Mathlib and already proved source-library torsion membership lemmas.
Remote single-file compilation checks the proof; delivery preflight checks its axioms.

## No longer needed

No imports removed; no nodes or modules pruned. Every declared proof dependency remains
used as a definition, tensor-localization tool, or localization realization.
The explicit kernel/cokernel bounds for M → M tensor_A B and the intermediate
M_a tensor_L L identification in the former proof plan are unnecessary: working directly
with L tensor_A M and its localization map gives the kernel criterion immediately.
Those steps had no separate statement modules to withdraw.

## Where the brief, the DAG or earlier work was wrong

No false statements found. The earlier DAG plan is correct but longer than necessary.
The assumptions a ∈ I and x ∈ nonZeroDivisors A are retained verbatim; the proof only
needs B to be an A-subalgebra of A_a and x to act injectively on M.
The proof handles a = 0, nilpotent a, the zero ring, and M = 0 because the localization
criteria and scalar regularity lemmas allow subsingleton targets.
Searches via leanfinder, loogle, grep and direct source inspection found the Mathlib
tensor-localization instance and `IsSMulRegular.of_isLocalizedModule`; no duplicate
of the exact chart torsion comparison was found. The unit route is preserved.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
