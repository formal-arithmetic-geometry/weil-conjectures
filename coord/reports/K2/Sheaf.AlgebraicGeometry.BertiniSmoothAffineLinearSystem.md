## What changed

Implemented `AlgebraicGeometry.exists_smooth_affine_prescribedPoint_linearSystem`
without changing its signature or existing public imports. Its private helpers construct
the projective chart from the source library's proved
`Proj.exists_isClosedImmersion_chart`, establish the tensor unit's semilinearity and
composition equation, and enumerate the finite kernel basis. The main proof establishes
linearity, vanishing on the prescribed points, the coefficient-open transport, and all
smoothness, affineness and pure-dimension conclusions from the existing eventual
smooth-system theorem. A general coordinate-invariance theorem supplies only the
remaining generating-family/projective-immersion transport.

Added private proof imports of `BertiniPrescribedPointSmoothSystem`,
`GeneratingSectionsImmersionReindex`, `ProjectiveSpace.CoordinateModel`, `Regular`,
and `SectionNonvanishingZeroLocus`. No source-library file or existing definition changes.
Updated the assigned node's proof and proof dependencies to match the Lean assembly.
The assembled module compiled on the server in 19.4 seconds; the new module also
compiled independently. A final style-only local-instance cleanup removes the sole
warning, and delivery preflight verifies the exact delivered files and their axioms.

## Proved and sorry left

Closed the original whole-proof hole in
`AlgebraicGeometry.exists_smooth_affine_prescribedPoint_linearSystem`
(node `lem-zl-bertini-smooth-affine-linear-system`). Its module has zero direct holes.

Added one whole-proof hole:
`AlgebraicGeometry.ProjectiveSpace.generatingSections_immersion_iso_reindex`
(node `lem-zl-generating-sections-immersion-iso-reindex`), in its own new module.
It asserts invariance for two already-specified line bundles and finite families,
without any Bertini or geometric existence conclusion. Thus this delivery is a
decomposition: one hole closed, one strictly smaller hole added, net zero holes closed.
All private helpers are proved. No sorry occurs inside any construction or definition.

## No longer needed

No imports or dependency modules are pruned. The original dependency
`lem-zl-bertini-prescribed-point-smooth-system` remains used. Its jet-surjectivity clause
is not used directly by this assembly, but remains needed inside the smooth-system
proof, so no jet dependency is claimed to be pruned.

## Where the brief, the DAG or earlier work was wrong

The compactification and module/coordinate transports were marked elementary in the
previous plan. The compactification and tensor transport are now actual proved Lean.
The remaining index/module invariance of the projective morphism has no existing API
found in Mathlib or the two project roots; it is isolated explicitly rather than
repeating the affine-system existence theorem. The unit route is preserved.

Elaboration initially unfolded large Proj and projective-space constructions while
inferring the projective-chart theorem's parameters. Explicit type parameters and local
irreducibility annotations removed this bottleneck; no timeout limit was raised.

## New nodes

`lem-zl-generating-sections-immersion-iso-reindex` records the section-preserving
isomorphism and finite coordinate permutation step, sourced to Stacks Tag 01NE and
the blueprint's basis-coordinate construction. Searches used LeanSearch, Loogle, and
local Mathlib/source/project-module grep. Empty schemes and empty index sets are
covered: an empty generating family forces the source scheme to be empty. The result
is independent of compactification, prescribed points, smoothness and dimension.

Change record: `coord/changes/K2-bertini-generating-system-reindex.md`.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
