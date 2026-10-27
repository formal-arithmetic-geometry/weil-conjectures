## What changed

Proved `AlgebraicGeometry.Scheme.Hom.relativeDifferentialSheaf_baseChange` in
`Sheaf.AlgebraicGeometry.RelativeDifferentialSheafBaseChange`. The public theorem statement,
the open-subscheme abbreviation, and all public imports are unchanged. Six proved private
helpers construct the normalized global map, prove finite type, identify the affine
section-ring pushout, transport ring base change, normalize affine pullback sections,
and prove the commuting affine comparison.

The proof uses the existing `TangentBundle` quasi-coherence instance,
`ModulePullbackAffineSections`, `RelativeDifferentialsAffineSections`,
`QuasiCoherentIsoOnAffineCover`, `QuasicoherentFiniteTypeAffine`, and Mathlib's
`KaehlerDifferential.tensorKaehlerEquiv`. The node's proof and dependencies now follow
this route. No new public declarations, changed definitions, or adapted consumers.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.Scheme.Hom.relativeDifferentialSheaf_baseChange`
(node `lem-trf-relative-differential-sheaf-base-change`). Added zero holes; zero holes
remain in the item. This is a proof, with no split-off statements.

The public theorem statement was checked textually against the repository version.
The complete module compiled successfully on the project server in 29.4 seconds
(exit code 0), below the 60-second limit. All five added source-library imports
passed the import-direction cycle check. The delivery command runs the independent
preflight and axiom checks before pushing.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.TensorPullbackOpenRestriction`
- `Sheaf.AlgebraicGeometry.AssociatedModulePullback`
- `Mathlib.RingTheory.Kaehler.Basic`
- `Mathlib.AlgebraicGeometry.Modules.Tilde`
- `WeilConjectures.Topology.GlueSheavesOfModules`
- `WeilConjectures.Topology.SheafIsomorphismLocalOpenCover`
- `WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType`

The direct DAG proof dependencies no longer need
`lem-weil-pbc-open-immersion-module-pullback-restriction`,
`lem-weil-pbc-associated-module-pullback`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`,
`lem-weil-pbc-spec-module-tilde-sections`,
`lem-weil-pbc-glue-sheaves-of-modules`,
`lem-weil-pbc-sheaf-isomorphism-local-open-cover`, or
`lem-weil-pbc-module-pullback-finite-type`.

The global map comes from the universal derivation, so explicit local gluing and its
overlap-localization calculation are unnecessary. The general affine tensor-sections
interface subsumes the source comparison. Finite type follows by applying the affine
criterion separately to f and its locally finite type base change. Tilde and local
isomorphism tools remain indirect dependencies of existing library results. No whole
library module is withdrawn. Existing tool approvals and historical split/review
records are unchanged; only the proof, proof dependencies, and proof origin are updated.

## Where the brief, the DAG or earlier work was wrong

The previous plan overlooked the proved general affine tensor-pullback sections
interface and the direct global universal-derivation construction. These shorten the
proof while preserving every clause and the unit route. No statement error was found.
The construction and affine-cover argument include empty schemes, zero rings,
arbitrary non-flat base changes, and zero algebra generators.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
