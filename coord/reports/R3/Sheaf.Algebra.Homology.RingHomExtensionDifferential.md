## What changed

Proved `CategoryTheory.ringHomExtension_differential_adjacent` in
`Sheaf.Algebra.Homology.RingHomExtensionDifferential`. Private proved helpers establish
naturality on pure tensors, tensor extensionality, and the two-term differential
calculation. The existing all-degree theorem combines the adjacent calculation with
vanishing off the complex shape.

Repaired the return at head `ca57320f6a`: the retained definition repair imported the
retired `Sheaf.Algebra.Homology.HomComplexProjections`. It now imports the current
source module `WeilConjectures.Algebra.Homology.HomComplexProjections`.
`RingHomExtensionDefs.ringHomComplexProjection` obtains the same chosen projections
from this folded specification. Every existing public signature is preserved.
The shared-definition change and complete consumer inventory are recorded in
`coord/changes/R3-ring-hom-projection-api.md`. No source-library file is edited.

## Proved and sorry left

Closed one existing hole: `CategoryTheory.ringHomExtension_differential_adjacent`
(node `lem-pc-ring-hom-extension-differential-adjacent`).
`CategoryTheory.ringHomExtension_differential` was already proved and now uses the
completed adjacent calculation. Zero holes added, zero holes left in both delivered
modules, zero split off. Every private helper is proved.

## No longer needed

Removed the redundant proof imports
`WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct` and
`WeilConjectures.Algebra.Homology.HomComplex` from the item: the shared definitions
already provide both. The shared definitions replace their direct public import of
`HomComplex` by its public re-export through the current upstream `HomComplexProjections`.
No mathematical prerequisite module is pruned.

The adjacent node's circular proof dependency on its own all-degree parent is
replaced by the foundational Hom-complex, tensor-product and projection dependencies
actually used. No upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The retained packet referenced a retired `Sheaf` projection module. The repair uses
its current upstream counterpart. The original adjacent node also cited the parent
theorem whose existing proof already invoked the adjacent theorem.

The calculation separates canonical projection data from its specification proofs.
Local irreducibility settings keep the chosen functor and pure tensors folded during
the generic calculation. Trying to use the original unfolded existential specification
with the unchanged shared definitions exceeded the 60-second limit; the folded API
compiled the completed differential proof in 37.5 seconds with profiling enabled.
Profiling settings were removed afterward. No new node or mathematical statement
is introduced.

Validation of this repaired packet: both delivered modules compiled; the differential
module took 22.3 seconds without profiling. All seven external textual projection
users (`BoundedRingHomExtensionDegree`, `PerfectRingDualTermFlat`,
`PerfectRingHomTensorDegreeCondition`, `PerfectRingHomTensorDifferential`,
`PerfectRingHomTensorPostcomposition`, `PerfectRingHomTensorPrecomposition`,
`RingHomExtensionDegrees`) and the direct consumer `NormalizedRingHomExtension`
compiled unchanged, with no errors or warnings (2.5 to 36.7 seconds).
The import-direction check confirms the upstream projection import creates no cycle.

## Second reading by R3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
