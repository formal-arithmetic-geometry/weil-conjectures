## What changed

Proved `AlgebraicGeometry.Scheme.StrictSupportNormalization.refinement_cocycle` in
`Sheaf.Paper.StrictReductionCompactSupportNormalization`. The proof applies
`cbcRefinementMap_functoriality` to the ambient completed-ring input, maps its
identity and composition laws through the actual quotient-reduction functor, and
cancels the specified `supportReduction` corners. Each supplied compactification
provides separatedness and local finite type of the morphism. Thus no completeness
or finite-origin assumption is added.

Added a proof-only import of `Sheaf.Paper.CompleteCompactSupportProetale` and updated
Step 9, `proof_deps`, and `proof_origin` of the assigned node to name
`lem-cbc-completed-refinement-map-functoriality`. This existing node is used as a tool
from the compact-support unit: its ambient functoriality gives precisely the
identity and composition laws needed here, without an origin hypothesis. No new
nodes, definitions, or declaration signatures are introduced or changed.

## Proved and sorry left

Closed one of the item's thirteen original holes:
`AlgebraicGeometry.Scheme.StrictSupportNormalization.refinement_cocycle`.
Added zero holes and split off zero statements. This is a proof from the existing
named theorem `AlgebraicGeometry.Scheme.cbcRefinementMap_functoriality`, whose own
proof remains an existing hole outside this delivery.

The twelve retained holes, all in namespace
`AlgebraicGeometry.Scheme.StrictSupportNormalization` and attached to
`lem-pur-strict-reduction-compact-support-normalization`, are:

- `strictReductionCompactSupportNormalization`
- `scalarPull_composition`
- `inputPull_composition`
- `refinement_normalization`
- `targetRefinement_normalization`
- `refinement_exchange`
- `inputPull_identity`
- `refinement_isIso`
- `commonRefinement_normalization`
- `commonRefinement_coherence`
- `scalarPush_composition`
- `sourceRefinement_normalization`

The full delivered module compiled cleanly in 31.5 seconds through `lcompile.py`.
The added import is acyclic, and the new proof dependency creates no DAG cycle.

## No longer needed

None. All original public imports and dependencies of the unfinished clauses remain.
The unit's route is retained; no module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous attempt's five unvalidated refinement proof bodies still hit expensive
kernel conversions across the constant and completed tower presentations. Diagnostic
runs tested generic categorical proofs, explicit category parameters, wrapper
annotations, and generalization. Those bodies are preserved in the sandbox scratch
files and are not counted as proofs or included in the delivered Lean module. No
profiling or temporary heartbeat settings are delivered.

The earlier missing-artifact failure is no longer present. A refreshed published
build now provides `cbcRefinementMap_functoriality`; this supplies a direct proof of
the strict refinement cocycle on arbitrary ambient input. The original node already
mentioned conjugating the original reduction maps as an alternative; the updated
Step 9 now names its precise existing dependency.

The main exchange normalization still needs an identification of the constant
ringed-square mate with the proper-square mate used by `compositionE`. Its named
hole is retained without changing the statement.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
