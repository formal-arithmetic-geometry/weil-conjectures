## What changed

Completed `AlgebraicGeometry.nagataDensityNormalizationSetup` in
`Sheaf.Compactification.NagataDensityNormalizationSetup`, preserving its statement and
all public imports. The proof follows the existing six-step node plan: use the
Noetherian and quasi-compact-immersion instances; give the schematic image and the
complement their induced Noetherian topologies; prove disjointness by the canonical
image factorization; use `Scheme.isEmpty_pullback`; identify the other pullback
projection using the explicit inverse `(id_X, c.i.toImage)` and cancel the
closed immersion to obtain the second projection formula. Properness follows from
the closed-immersion and composition instances.

The geometric argument and the unit route are unchanged. No definitions, signatures,
DAG dependencies, or consumers change.

## Proved and sorry left

Closed the one existing hole in
`AlgebraicGeometry.nagataDensityNormalizationSetup`
(node `det-nagata-density-normalization-setup`). Holes closed: 1; holes added: 0;
split off: 0. No `sorry` remains in the delivered module, and no other Lean module
is added or changed.

## No longer needed

Removed the unused private proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant`.
The needed density instance is already provided by the public import of
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` through
`WeilConjectures.ConstructibleSheaf.OpenClosedStratification`. No declared DAG
proof dependency is bypassed, and no module or node is withdrawn. No claim is made
that the removed import's module is globally unreachable.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The supplied plan is implemented directly
using existing Mathlib and source-library results; hereditary topological
Noetherianity packages the closed-subspace compactness argument. The pullback
isomorphism uses the explicit inverse from step 5 of the node.
The theorem requires neither reducedness nor any additional hypothesis on the base.
The argument also applies when X is empty or the open immersion is the identity.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
