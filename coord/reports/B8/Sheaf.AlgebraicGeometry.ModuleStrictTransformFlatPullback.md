## What changed

Proved `AlgebraicGeometry.Scheme.Modules.existsUnique_moduleStrictTransform_flatPullback`
with its original signature and both original comparison constructions unchanged.
The proof follows all three steps of
`lem-trf-module-strict-transform-flat-pullback`: use
`blowupSquare_pullback_quotientData`, identify its map by the two pullback projections,
apply `supportedSectionsKernel_flatPullback`, transport supported sections through the
specified ordinary-pullback isomorphism, and pass to cokernels. Uniqueness follows by
cancelling the pulled-back quotient epimorphism.

Three proved private helpers express the elementary sectionwise kernel argument,
naturality under an isomorphism, and the supported-kernel theorem in terms of its open complement. No new public declaration, instance, statement,
definition, node, or change record is introduced. All public imports remain unchanged.
The two declared geometric and supported-kernel dependencies are added as proof imports,
together with the sectionwise-kernel and categorical cokernel APIs they require.

The complete proof compiled without errors or warnings in 14.8 seconds.
The redundant explicit `Preserves.Shapes.Zero` import was then omitted because
`Preserves.Shapes.Kernels` publicly imports it; delivery recompiles the final file.

Searches used the prescribed leanfinder, loogle and grep tools, and direct searches of
Mathlib and both library roots. Mathlib supplies `PreservesCokernel.iso` and
`cokernel.mapIso`; no existing strict-transform flat-pullback theorem was found.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.Modules.existsUnique_moduleStrictTransform_flatPullback`
(node `lem-trf-module-strict-transform-flat-pullback`).

One hole closed, zero holes added, zero split off, zero holes remain in the item.
The imported declarations `blowupSquare_pullback_quotientData` and
`supportedSectionsKernel_flatPullback` retain their existing holes in their own modules;
this delivery proves the assigned assembly from these stated dependencies.

## No longer needed

Removed the following original proof-only imports:

- `WeilConjectures.Blowup.Principalization`;
- `WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde`;
- `WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSectionsBijective`;
- `Mathlib.RingTheory.Flat.Basic`;
- `Sheaf.AlgebraicGeometry.ModuleStrictTransform` (already provided by the public imports).

The geometric and affine flat-tensor work is supplied by the two existing dependencies,
so the parent does not repeat their proofs. All four current DAG proof dependencies
remain used, and the existing three-step route and unit route are preserved.
No node or module is withdrawn, and no transitive dependency is claimed globally pruned.
The separately stated `blowupSquare_strictTransform_quotientPresentation` is unnecessary
for this assembly: the strict transform and its quotient map are definitionally the
categorical cokernel and its projection.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The old module's direct affine-calculation imports
predate the DAG's extraction of the two existing dependencies; the proof imports now
follow the current DAG route. All changes are confined to the assigned module.

## Second reading by B8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
