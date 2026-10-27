## What changed

Proved `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_test_naturality`
by composing the existing general test section naturality and closed-unit evaluation
naturality declarations. Explicitly derive weak etaleness from each affine pro-etale test.
No new theorem or axiom is introduced. Extracted canonical maps unchanged to
`Sheaf.Paper.ClosedTestDerivedExchangeMaps`, publicly reexported from the item module,
to break the dependency cycle. Updated the definition node attachment and the theorem
node's proof route and proof dependencies.

## Proved and sorry left

Closed 1 of the item's original 4 holes:
`AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_test_naturality`.
Added 0 holes and split off 0 statements. The proof uses existing named theorems whose
proofs remain pending; this is a proof from the project's stated dependencies.

The following original item holes remain unchanged, all belonging to
`lem-sfb-closed-test-derived-exchange-model`:

- `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.section_comparison_base_change_naturality`.
- `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_coefficient_naturality`.
- `AlgebraicGeometry.ProEtale.ClosedTestDerivedExchangeModel.closed_test_derived_exchange_model`.

The two adapted dependency modules retain their existing holes, unchanged:

- `AlgebraicGeometry.ProEtale.ClosedTestSectionSteps.proetale_section_localization`
  (`lem-sfb-nonaffine-proetale-section-localization`).
- `AlgebraicGeometry.ProEtale.ClosedTestSectionSteps.closed_derived_evaluation`
  (`lem-sfb-nonaffine-closed-derived-evaluation`).

## No longer needed

No node or module is withdrawn. No mathematical dependency of the three unfinished
clauses is pruned. The proved test-naturality clause uses the two existing general
section results directly, and does not need resolutions or the combined localized-model
coherence theorem for that clause. The five original proof dependencies remain needed
by the unfinished clauses and remain recorded.

Both adapted dependency modules replace their import of the theorem module by its
canonical construction module. The original public imports of the item move to the
construction module and remain publicly reexported. The four existing private imports
for the already-proved restriction-localization calculation stay in the theorem module;
the new construction module does not need them. No public import exposure is lost.

## Where the brief, the DAG or earlier work was wrong

The existing proof interfaces need the parent's constructions, creating a Lean import
cycle if used directly from the parent theorem module. Separating unchanged maps from
theorems resolves this. Source: Stacks proetale.tex, lemma-closed-immersion-affines-apply
(Tag 09BL), and sites-cohomology.tex, lemma-unbounded-cohomology-of-open (Tag 0D6F).
LeanFinder and Loogle searches found only general adjunction/naturality interfaces;
local rg found the two exact existing section-naturality declarations.
The unit route is unchanged; no new split statement or replacement unit is introduced.

## Forced adaptations

`Sheaf.Paper.ClosedTestClosedEvaluation` (G9) and
`Sheaf.Paper.ClosedTestSectionLocalization` (H5) each change exactly line 8:
`public import Sheaf.Paper.ClosedTestDerivedExchangeModel` becomes
`public import Sheaf.Paper.ClosedTestDerivedExchangeMaps`.
Original lcompile.py --all error:
`the modules import one another in a cycle: Sheaf.Paper.ClosedTestClosedEvaluation,
Sheaf.Paper.ClosedTestDerivedExchangeModel, Sheaf.Paper.ClosedTestSectionLocalization`.
Both changes are required to remove the cycle; signatures, visibility and proofs stay
identical. The full consumer audit and verbatim old/new construction record are in
`coord/changes/S7-closed-test-derived-exchange-maps.md`.

## Forced adaptations

### Sheaf.Paper.ClosedTestClosedEvaluation
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

### Sheaf.Paper.ClosedTestSectionLocalization
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
