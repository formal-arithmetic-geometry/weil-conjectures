## What changed

Retired `Sheaf.AlgebraicGeometry.AffineSheafResolutionOfRingModel` in favor of the
already proved upstream base module and its `AffineSheafResolutionOfRingModelExtension`.
The sole remaining consumer, `Sheaf.AlgebraicGeometry.DescentFirstProperFlatCechModel`,
now publicly imports these two modules. Its statements, definitions and proofs are
unchanged. The three public signatures are identical to their upstream replacements.
The DAG node `lem-pc-affine-sheaf-resolution-from-ring-model` now points to the
upstream resolution theorem; the statement and proof plan are unchanged.

Validation: the adapted consumer compiled through lcompile.py in 11.2 seconds
without diagnostics. Source import-closure inspection checks no new twin collision
and no remaining importer of the withdrawn module. The retired twin clash is removed;
there are no newly introduced twin clashes. The delivery tool also runs the
axiom probe and preflight. No upstream source file or target statement is changed.
Change record: `coord/changes/retire-affine-sheaf-resolution-of-ring-model.md`.

## Proved and sorry left

The assigned module has zero holes before retirement. Closed 0; added 0; split off 0;
left 0 in this delivery. The resolution theorem
`AlgebraicGeometry.Scheme.Modules.exists_affine_sheaf_resolution_of_ring_model`
(node `lem-pc-affine-sheaf-resolution-from-ring-model`) and the extra declarations
`CategoryTheory.sectionsHomologyIso` and
`AlgebraicGeometry.Scheme.Modules.nonempty_affineSectionsHomologyIso` already have
complete proofs upstream. This is duplicate-module retirement, not a new proof.

## No longer needed

Withdrawn module: `Sheaf.AlgebraicGeometry.AffineSheafResolutionOfRingModel`.
Removed its public import from `Sheaf.AlgebraicGeometry.DescentFirstProperFlatCechModel`;
replaced it with upstream base and extension imports. All imports of the withdrawn
module disappear with its body; their needed declarations remain available through
the upstream modules. No mathematical dependency node is pruned: the same resolution
statement and plan remain in use through the upstream Lean attachment.

## Where the brief, the DAG or earlier work was wrong

The generic stage-3 brief describes a proof obligation, but the current queue assigns
this item as `retire`, with 0 holes. The retirement inventory said the upstream twin
lacked sectionsHomologyIso and nonempty_affineSectionsHomologyIso; both are now
present in AffineSheafResolutionOfRingModelExtension. The inventory listed two
consumers; ProperCohomologyFiniteFreeResolution was already retired before these
edits, leaving only DescentFirstProperFlatCechModel to adapt.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
