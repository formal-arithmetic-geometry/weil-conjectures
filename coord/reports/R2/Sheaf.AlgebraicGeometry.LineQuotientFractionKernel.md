## What changed

Copied the assigned module into the sandbox and added the proof-only import
`Sheaf.AlgebraicGeometry.LineQuotientFractionKernelSections`. The main theorem is
reduced by module-sheaf extensionality to a sectionwise vanishing equivalence.
The sectionwise affine fraction-chart calculation is stated as a separate lower
node and module.

## Proved and sorry left

The assigned theorem `AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_fraction_kernel`
combines the sectionwise result with real `SheafOfModules.hom_ext` and
`ModuleCat.hom_ext` calculations; no anonymous sorry remains in its proof.
One sorry remains in
`AlgebraicGeometry.ProjectiveBundleQuotientGeometry.lineQuotient_fraction_kernel_sections`,
node `lem-trf-line-quotient-fraction-kernel-sections`. This is a strictly lower
statement containing the affine chart and localization calculation.

## No longer needed

The theorem proof does not directly use the planned definitions of the Proj
standard-open cover or the normalized twisting-sheaf implementation; those are
encapsulated by `HasQuotientFractionCharts` and `pulledQuotient`. No existing
module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's local chart proof is substantially longer than the categorical glue
once the sectionwise statement is isolated. No statement or definition was
changed.

## New nodes

Added `lem-trf-line-quotient-fraction-kernel-sections` with source Tags 01OA and
01O4. It records the missing affine section calculation and is imported only by
the assigned module. Added `lem-trf-line-quotient-fraction-kernel-categorical`,
which records the elementary sectionwise zero criterion used to assemble the
parent morphism equality.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
