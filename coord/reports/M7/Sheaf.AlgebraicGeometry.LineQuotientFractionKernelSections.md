## What changed

Proved `AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_fraction_kernel_sections`
with its signature unchanged. Added proved private helpers for restriction of coefficients,
affine factorization, tensor induction, and the comparison on a unit-denominator chart.
The proof uses `lineQuotient_pulled_chart_normalization` and
`exists_tensorPullback_affine_sections`, then sheaf separatedness.
The localization inverse is a concrete inverse of the canonical localization isomorphism,
not data selected from an unproved existence statement. Generic private helpers keep the
large symmetric-algebra constructions out of kernel reductions.
Updated the item's proof plan and dependencies to this implementation.
Only the item module and its own DAG node are changed.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_fraction_kernel_sections`
(node `lem-trf-line-quotient-fraction-kernel-sections`).
Holes closed: 1. Holes added: 0. Sorries left in the delivery: 0.
No decomposition or split-off statement was added.
The completed proof compiled in 10.2 seconds without profiling options.
`#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the redundant explicit proof import
`Sheaf.TraceFormula.LineQuotientHomogeneousFractionMap`: the existing public import
`LineQuotientChartInverseData` already supplies its fraction-chart definitions.
The homogeneous-fraction-map existence/uniqueness theorem is not invoked; the given
chart predicate supplies its generator cover and degree-one fraction equations.
Its module and node remain needed for those definitions; no module or node is withdrawn.
No other planned dependency is pruned.

## Where the brief, the DAG or earlier work was wrong

The original one-step plan omitted the bridge from generator equations to arbitrary
sections: affine pullback sections are tensor sums, and frame coefficients extend the
equation by tensor induction. The implemented proof records that step explicitly.
The necessary chart normalization and affine sections theorems already exist, so this
obligation can be closed without another split. No statement or definition was changed.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
