## What changed

Filled `WeilConjectures.IntegralSystemRealization.integralOpenLimitComplete` in
`Sheaf.SixFunctors.IntegralOpenLimitComplete`, preserving its statement and public imports.
Normalized reconstruction supplies completeness of the source limit. The proved
`dvrOpenModel_exists` and `dvrOpen_complete` helpers supply the actual DVR open model
and preservation of completeness. `openDvr_ringed_identification` identifies its
extension with `ringedOpen`. The proved local principal criterion and its isomorphism
invariance transport completeness to the required object.

Added only private proof imports, using `import all` where existing proved private
helpers are needed. Updated the item's proof steps and dependencies to match.
No other existing module, definition, statement, attribute or instance was changed.
The remote proof compile completed in 4.0 seconds; the delivery checks validate the
final lint-clean version and its axioms.

## Proved and sorry left

Closed 1 of 1 holes: `WeilConjectures.IntegralSystemRealization.integralOpenLimitComplete`
(node `lem-sf-integral-open-limit-complete`). No holes remain in the item, no holes
were added, and no statements were split off. The reused helpers are already proved.

## No longer needed

The recorded proof dependency `lem-sf-integral-open-extension-complete`
(`Sheaf.SixFunctors.IntegralOpenExtensionComplete`) is not needed by this proof.
Its public theorem requires invertibility of l on both schemes and takes a different
operations presentation. The existing DVR model and identification avoid both pieces
of glue and work on the actual theorem domain. This is a proof-dependency removal;
the inherited statement-dependency record and other users remain, so no whole module
is claimed globally pruned. No existing public import was removed. Every added proof
import supplies a declaration used by the proof.

## Where the brief, the DAG or earlier work was wrong

The recorded open-preservation theorem cannot directly be applied: its scheme-unit
hypotheses do not follow from this item's hypotheses. Already proved private helpers
in the DVR reconstruction modules remove the apparent obstruction without changing
any theorem statement or adding another obligation. Only hN's normalization component
is needed; the output Good hypothesis remains in the unchanged signature.
The unit's compatibility route is preserved, including the actual completed ring and
its quotient-normalized open identification. The zero object, empty open and identity
open remain covered by the general model construction and preservation arguments.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
