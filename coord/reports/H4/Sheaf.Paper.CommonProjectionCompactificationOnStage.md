## What changed

Restored the assigned module from its quarantine archive, preserving its public import,
statement and Lean attachment. Replaced the body of
`WeilConjectures.commonProjectionCompactification_onStage` by a complete categorical
transport proof. Added only a private proof import of
`Sheaf.Paper.CommonProjectionTensorCompatibility` to the item.

The proof obtains one shared natural tensor comparison, applies tensor naturality to
its source endpoint, and uses the prescribed coefficient compactification square at
both endpoints. Applying inclusion to `hH.compactification` and cancelling the source
endpoint isomorphism gives the unchanged conclusion. The four proved private helpers
are the generic refinement calculation already present in the rational analogue,
reused here without importing that analogue's entire coherence proof and dependencies.

Added `WeilConjectures.commonProjectionTensorCompatibility` in its own new module.
It states only that inclusion preserves each individual compact-support projection
through one natural tensor comparison independent of the compactification. Its
witness is destructed inside the proof of a proposition; no definition chooses data
from a mere existence theorem. Updated the assigned node's proof and proof dependencies
and added the new lemma's node.

## Proved and sorry left

Closed the item's original hole:
`WeilConjectures.commonProjectionCompactification_onStage`
(`lem-sf-common-projection-compactification-on-stage`). Its module has zero remaining
`sorry`s. All four private tensor/refinement/transport helpers are completely proved.

Added one hole:
`WeilConjectures.commonProjectionTensorCompatibility`
(`lem-sf-common-projection-tensor-compatibility`), whose proof is exactly `by sorry`.
Its source and full proof in words are in its docstring and node.

This is a decomposition: one upper hole closed, one strictly local mate-compatibility
hole added, net zero holes. The lower lemma contains no finite-stage coherence
hypothesis and no compactification comparison equation. The real refinement and
cancellation calculation combining it with the finite-stage equation is complete.
The existing rational compatibility theorem in the imported endpoint-API module is
unchanged, and is not invoked by this proof.

## No longer needed

No original import is removed, and no module or declaration is withdrawn. No existing
node is globally pruned. The derived tensor and completed tensor/pullback normalization
nodes are no longer direct proof dependencies of the item: their local mate calculation
is isolated in the new compatibility lemma, which still needs those constructions.
The original algebraically closed coefficient dependency remains in the statement and
in the local lemma. No compactification, composition or proper-coincidence theorem is
used to prove that local lemma, so there is no circular appeal to coherence.

## Where the brief, the DAG or earlier work was wrong

The source was quarantined rather than withdrawn; its `coord/rework.tsv` row and archive
were checked before restoration. Its original one-step proof plan left implicit the
choice of one tensor comparison working across compactifications. The tensor field of
`SixFunctorExchangeComparison` is chosen per compactified square. Its projection field
alone therefore cannot be substituted twice into the coherence equation with a single
shared tensor comparison. The new lemma isolates exactly that local normalization
calculation. The completed categorical proof makes explicit the rest of the old plan.

The blueprint route is retained; `sk-rem-sf-pf-done` has no realized statement or step
bypassed by this calculation. No shared definition, signature, instance, attribute,
public import, source-library declaration, or target statement is changed.

## New nodes

`lem-sf-common-projection-tensor-compatibility` states the single-mate preservation
square for the prescribed coefficient inclusion, with one tensor natural isomorphism
independent of the compactification. It comes from the Compatibility paragraph of
`thm-sf-pf-field.proof.md`. Its proof constructs the inclusion tensorator from finite
representatives, identifies the canonical proper/open tensor/pullback maps, transposes
using the preserved counit and unit, and pastes those two squares. Equal and identity
coefficient extensions, zero objects and empty schemes use the same formulas. Searches
found the rational analogue, per-square coefficient comparisons, and a canonical
component tensorator, but no shared common-stage mate compatibility theorem. There
are no change records because no existing interface or other module is changed.

## Second reading by H4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
