## What changed

Reduced `AlgebraicGeometry.EmbeddedResolutionHistory.normalized_resolution_word_gluing`
to two geometric steps, each in its own new module: the coherent prescription on finite
admissible histories, and finite image plus local upper bounds for a given simultaneous prescription.
The original theorem signature is unchanged. Its complete combining proof obtains the
engine word's leading rational one from `R.normalized`, proves closedness by an explicit
open-complement argument, and proves summation preserves/reflects comparisons by expanding
the two lexicographic products and checking bottom separately. The comparison proof works
for every word and every D, without using the dimension bound.

Moved the original alphabet and chart declarations verbatim to
`Sheaf.AlgebraicGeometry.NormalizedResolutionWordCharts`, publicly re-exported by the
original item module. Only blueprint tags change. The relocation prevents an import cycle;
it changes no definition, signature or field. Change record:
`coord/changes/resolution-word-chart-module.md`.

## Proved and sorry left

The item's one original hole is reduced:
`AlgebraicGeometry.EmbeddedResolutionHistory.normalized_resolution_word_gluing`
(node `lem-trf-normalized-resolution-word-gluing`) now has a complete Lean proof from
named statements. Its leading-one, closed-upper-level, and summation-comparison assembly
has no holes. Four private order lemmas are also proved.

Validation: all four delivery modules compile within 15 seconds each (the latest
preflight recompiles the documentation-only line wrap). All three original direct
importers compile unchanged against the delivery: `ResolutionWordMaximumCenterDescent`
(12.7 s), `ResolutionWordFiniteHistoryComparison` (13.8 s), and
`ResolutionWordProgressTermination` (14.6 s). Their sandbox copies were then removed.
A textual check confirms all moved declaration bodies are identical except blueprint
tags and the original theorem signature is byte-identical.

Two holes are added, each the entire proof of a named public theorem in a separate module:

- `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_coherent_prescription`
  (`lem-trf-resolution-word-coherent-prescription`): original geometric steps 2--5,
  chart availability and independence with the regular bottom prescription. It has no
  finite-image, local-bound, closedness, or summation conclusion.
- `AlgebraicGeometry.EmbeddedResolutionHistory.resolution_word_finite_local_upper_bounds`
  (`lem-trf-resolution-word-finite-local-upper-bounds`): original geometric steps 2 and
  6--7 for an arbitrary family coherent on all its admissible histories, applied to one stage. It does
  not construct a prescription, assert arbitrary upper-level closedness, or compare sums.

Counts: one original hole removed, two added; zero holes left in the item; two in the
delivery. This is a decomposition, not a net hole reduction. The split statements have
sources, complete proof plans in docstrings and matching nodes. No data is defined by
choosing an arbitrary witness of an unproved existence theorem; the existential family
is eliminated only within the proof of an existential proposition.

## No longer needed

Removed the item's direct proof imports of `WeilConjectures.Blowup.Affine.Defs`,
`Sheaf.TraceFormula.ReducedSchemeImage`, `Mathlib.AlgebraicGeometry.Noetherian`,
`Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen` and
`Mathlib.Topology.NoetherianSpace`. They belong to the remaining geometric arguments,
whose node proof dependencies retain the corresponding statements. They are not pruned
mathematical work. The old five public imports are re-exported by the chart support module;
the two new lemma imports are private proof imports.

No mathematical dependency node or existing module is pruned. In particular the finite-type,
blowup, strict-transform, reduced-image, presentation, comparison, numerical-engine and
Noetherian/openness inputs remain necessary in the two geometric subarguments. The parent
node now cites those subarguments and the dimension-profile input used in the Lean order
proof instead of duplicating their dependencies directly. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The first preflight found a node-metadata formatting mismatch: the signature reader
records an inferred-type abbreviation as `abbrev ResolutionWord`, without its body. The
new definition node's `lean.statement` now matches that output. Its mathematical statement
still describes the actual definition. The change record also includes the refreshed full
transitive consumer set, including `ResolutionInvariantCalculus`.

No statement correction is made. The numbered original proof leaves two substantial
assembly tasks after its inputs are stated: constructing compatible admissible retained-head
charts, and descending the local engine bounds over the intrinsic head strata. These are
now explicit separate obligations rather than hidden inside the theorem's one `sorry`.

Edge cases checked in the split: empty stages have no chart obligations and empty image;
regular points receive bottom and cannot have a chart because `ResolutionWordChart.singular`
excludes them; old boundary members use truncated relative birth zero and retain their
absolute order; identity blowups remain in earlier-center lists; a head drop restarts the
presentation rather than using an empty old cosupport. Summation handles negative integer
entries, D = 0, all pairs of bottom/nonbottom values, and different heads or tails.

WANTED (already recorded in the source node): Bierstone--Milman--Temkin, arXiv:0905.3580,
sections 6.1--6.3. ILO VIII 2.3.11 and 2.3.13, printed pp.93--94 (PDF pp.99--100), only
refer to this construction; the geometric proof plans remain marked agent-written.

## New nodes

`def-trf-resolution-word-charts` attaches the original alphabet, summation, fresh-boundary,
stage-map, earlier-center, chart, tail and word definitions in their new support module.
Their bodies are unchanged.

`lem-trf-resolution-word-coherent-prescription` isolates the finite-history geometric
construction and compatibility, with no topology or summation conclusion.

`lem-trf-resolution-word-finite-local-upper-bounds` isolates finite image and neighborhood
upper bounds on one coherent admissible stage. The original module proves the closedness
consequence rather than adding another hole for it.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
