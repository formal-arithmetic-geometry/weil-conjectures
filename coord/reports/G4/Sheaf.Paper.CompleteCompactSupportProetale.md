## What changed

Filled the `cbcRefinementMap_functoriality` theorem by reducing its identity and composition clauses to two named component lemmas. The two component lemmas are recorded in the same item module because their statements use the module-local canonical refinement construction. No imports were added or removed.

## Proved and sorry left

The existing `completeCompactSupportProetale_isIso`, `completeCompactSupportProetale_identity`, and `completeCompactSupportProetale_compactifications` proofs remain complete. The `cbcRefinementMap_functoriality` theorem is now proved from its two strictly smaller component statements. Two new named proof holes remain: `cbcRefinementMap_identity_component` and `cbcRefinementMap_composition_component`. The pre-existing holes remain in `completeCompactSupportProetale_horizontal`, `cbcRefinementMap_isIso`, `completeCompactSupportProetale_refinement`, `completeCompactSupportProetale_vertical`, and `completeCompactSupportProetale_composition_refinement`.

## No longer needed

None. The existing imports and dependency nodes remain needed by the module and by its other coherence clauses.

## Where the brief, the DAG or earlier work was wrong

The DAG assigned the whole refinement identity/composition conjunction to one hole even though the canonical construction naturally separates into independent identity and composition component equations. The delivery records that decomposition without changing the theorem statement.

## New nodes

`lem-cbc-completed-refinement-map-identity-component` records the identity component equation used by the theorem. `lem-cbc-completed-refinement-map-composition-component` records the composition component equation used by the theorem. Both are genuine strict subclaims of `cbcRefinementMap_functoriality` and carry the source-level mate-pasting proof plan.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
