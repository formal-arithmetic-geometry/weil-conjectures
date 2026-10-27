## What changed

Proved `AlgebraicGeometry.Etale.relativeKummerExchange_edge` in
`Sheaf.AlgebraicGeometry.RelativeKummerExchangeGenerators` from the actual derived
adjunction, exact-pullback cohomology comparisons, canonical constant/single comparisons,
and shift compatibility of the specified base-change mate. The proof stays in the
ordinary derived category with module coefficients throughout.

To avoid repeated kernel conversion of concrete derived-category instance expressions,
construct the same data over a general coefficient category and specialize it by
abbreviations. The four existing result propositions are abbreviation specializations
of public, fully proved generic theorems; their hypotheses and conclusions are unchanged.
All existing docstrings are retained. A proved general cancellation lemma and local square/adjunct calculations keep the
comparison proof together, avoiding repeated kernel conversions. No custom tactic or
proof-term transformation is used.

The change is recorded in `coord/changes/kummerExchangeGenericInterfaces.md`.
Added a public import of the source's canonical shift instances and four private proof
imports for mate, shift, constant-composition and single-derived coherence. Updated the
existing DAG node's proof, proof origin and Lean attachments. No new node or module.

## Proved and sorry left

Closed 1 original hole: `AlgebraicGeometry.Etale.relativeKummerExchange_edge`
(node `lem-pur-relative-kummer-exchange-generators`). The module contains zero remaining
`sorry`. Added zero holes and split off zero statements. The unit identity, generator
criterion and degree-zero criterion are still fully proved, now generically and then
specialized. No target signature changes.

The complete candidate compiled in 48.3 seconds.
Reviewer check (2026-10-25): the three modules that name changed declarations
(NormalizedKummerGlobalArrows, NormalizedKummerCohomologyArrows,
NormalizedKummerGeneratorArrows) compile unchanged against this module. Restating the four
results as `theorem`s with explicit statements exceeded the 60 s compile limit. The edge,
generator and degree-zero docstrings now describe the route the proof takes.

## No longer needed

No original imports removed and no modules or nodes withdrawn. The proof follows the
current DAG's direct ordinary-derived route. The older scalar-forgetting, chart and
bounded-below route had already been removed by the previous delivery, so this packet
claims no new pruning for it. Temporary ProjectionFormula.Reduction experiments are not
imports in the delivery and are not claimed as pruning.

## Where the brief, the DAG or earlier work was wrong

The direct argument in the current DAG is correct. The original edge docstring describes
the older scalar-forgetting route; the retained statement is instead proved by the direct
canonical-comparison route in the current node. Large concrete category-instance terms
made an otherwise complete proof exceed the compile limit; generic construction and
local comparison calculations fix this without changing the mathematical maps.

## Second reading by U6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
