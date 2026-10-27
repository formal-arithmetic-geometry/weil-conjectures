## What changed

Restored the assigned module from its current quarantine archive, preserving the
published theorem statement and its public import. Replaced its sole `sorry` by a
proof of all three conclusions from explicit constant-family steps. Two geometric
steps are split off; the generic base-change step is proved in Lean.

The restriction argument is written in Lean: normalize both family comparisons at
one, use detection at one to equate their conjugates, evaluate at zero, and cancel
the resulting isomorphism squares. The private lemmas `counit_naturality`,
`reading_naturality`, `ratio_square`, and `normalized_readings_square` contain this
categorical argument. The base-change conclusion applies the generic constant-family
reading square and then the same proved ratio calculation. The rank-zero conclusion
uses uniqueness of the constant model and the geometric endpoint calculation.

Added two private proof imports, `PurityConstantFamilyBaseChange` and
`PurityRankZeroFamilyReadings`; their public statement imports supply
`PuritySectionConstantTrivialization`. Each new module has one named theorem with a complete proof in words and a matching node. The new
`lineCounit` is an explicit construction from the published pro-etale derived
composition, equality and identity isomorphisms; no data is selected from an
unproved existence assertion. Updated only proof fields of the assigned node.

The first bridge has no naturality assertion. It states constancy, its one
normalization, its zero-reading formula for the fixed delta, and one-fibre
detection. The second bridge concerns arbitrary line-family objects, not delta,
normal cones or exceptional comparisons. It isolates base-change coherence of
pullback and the use of detection at one. The third bridge concerns the actual
rank-zero endpoint maps, without mentioning delta. Thus none is the original
obligation with its hypotheses repackaged.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurityFiniteSetting.SectionRestriction.section_normalized_specialization`
(node `lem-pur-section-normalized-specialization`). Its proof contains no `sorry`.

Added two holes, one per named theorem:

- `WeilConjectures.PurityFiniteSetting.SectionRestriction.section_constant_trivialization`
  (`lem-pur-section-constant-trivialization`).
- `WeilConjectures.PurityFiniteSetting.SectionRestriction.rank_zero_family_readings`
  (`lem-pur-rank-zero-family-readings`).

Also proved the new
`WeilConjectures.PurityFiniteSetting.SectionRestriction.constant_family_base_change`
(node `lem-pur-constant-family-base-change`) from the source library
`ProEtale.leftDerivedUpperStarComp_assoc_app` and both identity laws. Private
helpers derive section coherence, endpoint naturality and the transport reading
equation, then the public proof uses detection at one and reads at zero.

This is a decomposition: one upper hole closed, two strictly smaller geometric
steps added, net one more textual hole. It does not establish a sorry-free
specialization theorem. All private helpers are proved. No definition contains a
hole. No existing declaration signature was changed.

## No longer needed

No module is withdrawn and no global dependency is pruned. No existing import was
removed. Removed the redundant newly added direct import of
`PuritySectionConstantTrivialization`; both new proof imports already provide it.
The original direct proof dependencies `prop-pur-dnc-family-constancy`,
`thm-pur-dnc-invariance`, and `lem-pur-dnc-section-geometry` remain needed through
the new steps; the item's direct proof dependencies now name those steps.
The smooth-purity unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The assigned path was initially absent from `lean/` because of the rework
quarantine, not because the statement was withdrawn. Restored its archived source
and retained its attachment and dependency route. During this session the shared
library restored the sources too; the dependency source matches the archive used
here. The recorded upstream cause was `Sheaf.AlgebraicGeometry.SfP1ChartExchange`.

The stated ordinary-etale family-constancy API does not directly provide the
pro-etale constant-model equation with the published endpoint maps. The first
new node isolates that transport, including its exact identity constraints. The
base-change step likewise requires compatibility of section evaluation with
pullback composition, proved in the second new node from the existing pro-etale
derived composition-coherence API. Neither endpoint square is silently assumed beyond the original theorem's hypotheses.

Edge cases checked mathematically: empty bases make the line-reading assertions
vacuous; rank zero retains the canonical collapse rather than identifying its
normal cone by definitional equality; arbitrary and nonflat base maps require
only pullback coherence, not exactness of tensoring with a base ring; detection
is restricted to isomorphisms from the specified family into pullback objects,
not arbitrary derived morphisms.

## New nodes

`lem-pur-section-constant-trivialization`, in
`Sheaf.Paper.PuritySectionConstantTrivialization`, isolates the transported
constant-family comparison, its delta zero-reading formula and detection at one.
Its source is DNC Local construction and Gluing and family-constancy normalization.

`lem-pur-constant-family-base-change`, in
`Sheaf.Paper.PurityConstantFamilyBaseChange`, isolates the canonical base-change
square of readings for arbitrary constant models, assuming detection at one.
Its source is the family-constancy base-change argument and derived pullback
composition coherence. This node is proved, not a remaining hole.

`lem-pur-rank-zero-family-readings`, in
`Sheaf.Paper.PurityRankZeroFamilyReadings`, isolates the polynomial zero-ideal
calculation with the actual counit-normalized endpoint maps. Its source is the
standard-pair Rees geometry, with no variables in rank zero.

No change record is needed: no existing interface or definition was changed,
and no other existing module or its node was modified.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
