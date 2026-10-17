## What changed

Repaired `AlgebraicGeometry.affine_derivedTensor_chart_comparison` against the current
K-flat and module-system APIs, preserving its signature and docstring. The proof
converts categorical module K-flatness to the acyclicity criterion, applies
`isKFlat_tilde` and `isKFlat_restrict`, specializes the natural K-flat derived tensor
comparison to singleton families, and composes with the chart total-tensor comparison.

The kernel helper is reused with a direct proof-only `import all` of
`WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`, rather than
through its retired Sheaf re-export. The explicit proof-only import of
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel` supplies
`Scheme.Modules.preservesLimitsOfSize_restrictFunctor`. No declaration or public
import changes. The copied node records these actual dependencies and proof steps.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.affine_derivedTensor_chart_comparison`
(node `lem-pc-affine-derived-tensor-chart-comparison`). Holes added: zero.
Holes remaining in the delivered module: zero. No intermediate theorem is split off.

## No longer needed

Removed `import all Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison`:
its private upstream helper must be imported directly from the upstream module.
The ordinary import of that upstream module is replaced by `import all`.
Removed the redundant proof-only import
`WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`, whose interface is already
provided by the existing public Abelian.Flat.KFlat import. No proof dependency node
is pruned: the upstream kernel-helper node and all K-flat/chart nodes remain used.

## Where the brief, the DAG or earlier work was wrong

The returned proof used the removed predicate `CochainComplex.IsKFlat`; the current
interface is `CochainComplex.IsAcyclicTensorKFlat`. Its `import all` targeted a retired
re-export and therefore did not expose the private upstream `tilde_preservesKernel`.
Finally, restriction's finite-limit instance belongs to `QuasicoherentKernel`, so that
module must be imported explicitly even when the upstream homology module imports it
for its own proof. These address all four compiler diagnostics in the return.

The retained attempt duplicated the upstream kernel proof. This repair removes that
duplicate and reuses the existing theorem directly. The attributed failing importer
in the return is the item itself; the two actual direct importers are additionally
checked unchanged against the repaired module: `AffineQCohTorAmplitudeDetection`
compiled in 32.2 seconds and `DerivedTensorPreservesQCoh` in 42.2 seconds. The repaired
item compiled in 30.0 seconds in that same run; no importer adaptation is necessary.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
