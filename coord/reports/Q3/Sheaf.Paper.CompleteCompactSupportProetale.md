## What changed

`Sheaf.Paper.CompleteCompactSupportProetale` now proves
`completeCompactSupportProetale_compactifications`. Naturality is proved from the
actual composite of whiskered natural transformations defining `cbcRefinementMap`.
Private categorical helpers prove independence of common refinement and arrows:
cofilteredness equalizes both arrow pairs, and the contravariant composition law
cancels the inserted invertible factor. A separate cancellation proves the cocycle law.
The proof-only import `WeilConjectures.Compactification.Cofiltered` supplies the
already proved arbitrary-base cofilteredness instance.

The original component formula caused naturality checking to expand derived-functor
data and exceed the compile limit. The actual canonical composite is now stored as
`cbcRefinementTransformation`, an irreducible natural transformation constructed
from the existing proper/open mate, inverse proper identity comparison, proper
compositor and equality of projections. The old `cbcRefinementMap` signature is
unchanged and its body takes the component of this stored transformation. Explicit
unitors and associators have identity components; functor map_id and category unit
laws reduce the new component to the original formula. Naturality is now the
structural field of this actual construction. The construction contains no `sorry`.
The full item compiled in 32.5 seconds. `CompactSupportExchangeDomains` compiled
unchanged with temporary profiling in 31.2 seconds against the repaired item, versus
42.6 seconds against the published item. Two further unchanged consumers passed in
40.0 and 59.8 seconds, and `WeilBaseChangeSemilinearPasting` passed in 30.6 seconds.
`StrictReductionCompactSupportNormalization` passed in 21.8 seconds. The only
consumer limitation is the pre-existing `ExchangeFunctoriality` timeout described
below; the change record lists every checked module.

The remaining geometric input for this clause is isolated as
`cbcRefinementMap_functoriality`: just the identity and composition equations for
actual refinement maps. It does not assert naturality, invertibility, choice
independence, or the cocycle conclusion. Existing declaration signatures and all
target statements are unchanged. No source-library module is changed.

The definition repair is recorded in
`coord/changes/cbc-refinement-natural-transformation.md`. Because a definition in
the targets' closure changes representation, the targets' statement review must
be reopened, although the canonical map and its mathematical meaning are unchanged.
No consumer has been edited.

## Proved and sorry left

Closed original hole:
`AlgebraicGeometry.Scheme.completeCompactSupportProetale_compactifications`.

Five original holes remain, all under `thm-cbc-complete-proetale`:

- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_horizontal`.
- `AlgebraicGeometry.Scheme.cbcRefinementMap_isIso`.
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_refinement`.
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_vertical`.
- `AlgebraicGeometry.Scheme.completeCompactSupportProetale_composition_refinement`.

Added one hole:
`AlgebraicGeometry.Scheme.cbcRefinementMap_functoriality`, under
`lem-cbc-completed-refinement-map-functoriality`. Its docstring and node give the
proper/open alpha normalization, mate-pasting, and compositor proof. The identity,
zero-object, empty-open, and complementary-component cases follow the same projector
normalization. The equations concern maps and do not require their invertibility.

This is a decomposition: one of six original holes closed, one new hole, five
original holes left, hence zero net holes removed among these declarations.
All private helpers are proved;
there are no new holes in definitions, and the new transformation is real composite
data. The naturality and cofiltered cancellation arguments are real Lean proofs, rather than extra assumptions of the new theorem.

## No longer needed

None. No existing import or dependency is removed. The strict refinement-coherence
and realization dependencies remain needed for the unfinished invertibility and
base-change interchange clauses. The unit's route remains intact.

## Where the brief, the DAG or earlier work was wrong

The strict refinement-coherence theorem concerns constant-coefficient tower maps;
it is not directly the required equation for the actual completed-ring maps.
The proposed endpoint-realization module imports this item, so importing that module
here would create a cycle. The new hole isolates only the two map-normalization
laws, while the categorical part of compactification coherence is proved directly.

The new statement is placed in the item's own module, the alternative explicitly
allowed by `coord/brief-stage3.md` section 3: its statement uses the actual
`cbcRefinementMap` defined in this module, so placing it in a new importing module
would create an import cycle when consumed here. It remains a separate DAG node and
a named public theorem, with a complete proof in words.

A broad dependency audit also encountered the pre-existing cycle at
`lem-pc-ring-hom-extension-differential`. Neither new node has a dependency path
back to this item; no new dependency cycle is introduced. This unrelated cycle is
reported here rather than changing other groups' nodes.

The unchanged consumer `ExchangeFunctoriality` has a pre-existing timeout. Its
profiled source took 71.1 seconds against the published item and 70.1 seconds against
the repaired item, both over the 60-second acceptance limit. The same first two
expensive `exact` steps account for approximately 36 and 45 seconds of cumulative
profiling in both runs. No Lean error appeared. This is reported for the maintainer;
no unrelated definition or consumer proof is changed. All profiling options and
counterfactual diagnostic sources are removed from the delivery.

The current blueprint changes this theorem to a condensed coefficient setting with
ordinary pullback on constructible objects. The existing node's `blueprint_update`
records that difference. This delivery leaves the assigned completed-coefficient
statements and all target signatures unchanged; it does not claim to resolve that
separate statement-review discrepancy. No new false statement was found.

## New nodes

`lem-cbc-completed-refinement-map-functoriality`, in
`dag/nodes/sec-smooth-purity/lem-cbc-completed-refinement-map-functoriality.json`,
states the unit/composition part of blueprint proof step 8, sourced from Stacks
0F7C and 0F7D with the ringed normalization calculation written out. Three kinds
of Mathlib search found no matching geometric identity. It is strictly smaller
than the five-part compactification-coherence theorem and is used by its complete
Lean assembly.

`def-cbc-completed-refinement-transformation`, in
`dag/nodes/sec-smooth-purity/def-cbc-completed-refinement-transformation.json`,
records the actual canonical composite before component evaluation, with no hole.
Its node gives the complete construction, source, and three kinds of Mathlib search.
The associated definition repair is recorded at
`coord/changes/cbc-refinement-natural-transformation.md`. No forced adaptation
has been made.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
