## What changed

Replaced the proof of `AlgebraicGeometry.exists_synchronized_resolution_zariski_descent`
by a complete Lean assembly from four strictly smaller geometric statements. The original
signature, universes, public imports and docstring are unchanged. All new imports are
private proof imports. No other existing Lean module, definition or statement changes.

The item now proves tower-map rigidity directly: induction on the levels reduces a
successor to `IdealSheafData.hom_ext_of_isInvertible_comap`, with invertibility supplied
by `isInvertible_comap_blowupMap` and flat pullback along the source blowup isomorphism.
This gives subsingleton cartesian comparisons over any fixed morphism. Applying the
same induction to the levelwise composite proves the cocycle equation without any
resolution or descent hypotheses. Full label preservation gives equality of label
ranges by bijectivity of finite-index casts.

The remaining geometric steps are padded overlap existence, existence of one regular
affine descent, comparison existence and ideal detection for such descents, and the
fact that the assigned embedded tower is an affine descent. The last three explicitly
assume the padded-overlap property, which is supplied separately. These statements
are not the original extension theorem under another name: none constructs its
simultaneous extension with the full collection of conclusions. The assembly also
proves empty-input triviality using a witnessing cover and `A.empty`, upgrades comparison
existence to `Unique` by the proved rigidity, and derives label equality for two covers
through their comparisons with the chosen global tower.

All five files compiled individually via `lcompile.py --all` (5.8--8.7 seconds in that
run). The final item compile passed without warnings in 4.4 seconds after removing two
`haveI` style warnings. No local
Lake commands or global builds were run. The DAG proof follows the actual Lean
assembly; the four new nodes preserve the parent's ten source steps below it.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.exists_synchronized_resolution_zariski_descent`
(node `lem-trf-synchronized-resolution-zariski-descent`). The item itself has zero
remaining `sorry` occurrences.

Added four holes, each exactly the proof of a named public theorem in its own new
module, with a source and complete natural-language argument in both docstring and node:

- `AlgebraicGeometry.ordinary_resolution_padded_overlaps`:
  `lem-trf-ordinary-resolution-padded-overlaps`.
- `AlgebraicGeometry.exists_affine_resolution_descent`:
  `lem-trf-affine-resolution-descent-existence`.
- `AlgebraicGeometry.affine_resolution_descent_comparison`:
  `lem-trf-affine-resolution-descent-comparison`.
- `AlgebraicGeometry.embedded_resolution_isAffineDescent`:
  `lem-trf-embedded-resolution-affine-descent`.

This is a decomposition: one upper hole closed and four lower holes added (net -3
holes closed), not a complete proof free of `sorry`. The rigidity, cocycle, empty-input
and label-range arguments themselves have no holes. No definition, instance, private
helper or anonymous statement contains `sorry`; no axiom was added.

## No longer needed

Removed these unused private proof imports from the item:

- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.AlgebraicGeometry.AffineFiniteTypeAlgebra`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `WeilConjectures.Blowup.Complement`
- `WeilConjectures.Blowup.Proper`

Their mathematical roles remain in the geometric sublemmas' DAG plans. None of the
original mathematical dependencies or modules is asserted to be globally pruned.
The item retains private imports of `WeilConjectures.Blowup.Principalization` and
`WeilConjectures.Blowup.BlowupUniversal`, which its rigidity and cocycle proofs use.
Public imports are preserved to avoid changing the existing interface.

The following former top-level tool approvals are no longer direct uses of the item
and were removed from its `tool_uses`; their uses remain below the four geometric nodes:
`lem-weil-pbc-finite-type-over-noetherian`,
`lem-weil-pbc-noetherian-open-subscheme-noetherian`,
`lem-weil-pbc-qc-open-immersion-finite-type`,
`lem-sfb-finite-type-composition-base-change`,
`lem-pqf-finite-affine-cover-qc-open`, `lem-pc-affine-finite-type-algebra`,
`sbc-lem-affine-space-smooth`, `lem-weil-pbc-affine-source-morphism-separated`,
`thm-nagata-blowup-flat-base-change`, `thm-nagata-global-blowup-complement`,
`lem-weil-pbc-affine-opens-basis`, `prop-nagata-global-blowup-cover-independent`,
`thm-nagata-global-blowup-proper`.

## Where the brief, the DAG or earlier work was wrong

The declared low-level dependencies give finite covers, affine presentations, flat
blowup base change, properness and uniqueness of blowup lifts. They do not themselves
state the tower-level padding, ideal descent and common-cover comparison steps. These
are now exposed as precise smaller Lean interfaces, rather than assuming that an
ideal-sheaf or blowup theorem already states synchronized tower descent. Their dependency
lists also explicitly carry the flat-base-change, padding and blowup-lift lemmas that
were supplied by preceding steps in the original single-node argument.

The DAG attachment of `thm-nagata-blowup-flat-base-change` is currently null, although
the published source has `IdealSheafData.blowupFlatBaseChangeIso` and the corresponding
`IsIso` instance in `WeilConjectures.Blowup.FlatBaseChange`. That unrelated node is not
modified here; its mathematical dependency is preserved.

Edge cases were checked against the new interfaces: empty base and empty covers,
empty overlap charts, unit centers on individual charts, proper ideals with isomorphic
blowup maps, empty label types, arbitrary label universes, and nonseparated inputs
without affine intersections. Deletion still tests the actual unit ideal. The new
comparison lemma assumes neither regularity nor uniqueness of an arbitrary descent;
regularity is local on its assigned cover, and uniqueness is proved separately.

The current unit and latest blueprint ancestor use the contracting-correspondence
route. This item is on the previously recorded historical resolution support branch;
this delivery neither changes that unit route nor withdraws any branch or module.

## New nodes

`lem-trf-ordinary-resolution-padded-overlaps` / `OrdinaryResolutionPaddedOverlaps`:
parent Steps 3--4, common full realization on triple affine overlaps, restoring precisely
unit-ideal stages. Source: ILO VIII 2.1.9 and Remark 2.3.5(ii), pp.88,92.

`lem-trf-affine-resolution-descent-existence` / `AffineResolutionDescentExistence`:
parent Steps 1--2 and 5--7, one regular affine descent for each input, conditional on
padded overlaps; no cover independence or uniqueness is concluded. Source: ILO VIII
2.2.11, 2.3.1 and Remark 2.3.5(ii), pp.91--92.

`lem-trf-affine-resolution-descent-comparison` / `AffineResolutionDescentComparison`:
parent Steps 5 and 8--9, nondeletion in a combined family, full comparison existence
and detection of actual center ideals; uniqueness and cocycle equations are excluded
and proved in the item. Source: ILO VIII 2.2.11 and Remark 2.3.5(ii), pp.91--92.

`lem-trf-embedded-resolution-affine-descent` / `EmbeddedResolutionAffineDescent`:
parent Step 10 with the cover/presentation prerequisites from Steps 1--2, the assigned
embedded tower admits a witnessing affine descent. Source: ILO VIII Remark 2.3.5(ii), p.92.

All inherit `sec-trace-formula` / `sk-i-curve-zero` and the parent's blueprint ancestry.
LeanSearch, LeanFinder and Mathlib grep queries are recorded from actual msearch runs.
Blueprint searches for ordinary blowups, synchronization and blowup descent found no
existing blueprint node stating these interfaces. Existing ordinary and normalized
descent modules were inspected; none supplies these conclusions for the given rule A.
No change record is required: no existing signature, definition or public import changed.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
