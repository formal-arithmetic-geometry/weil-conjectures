## What changed

Prove `AlgebraicGeometry.Scheme.cbcRealizationReductionInv_properties` by transporting
`cbcEndpointReductionInv_properties` along uniqueness of left adjoints. A proved private
transpose calculation compares the two specified maps through the unique adjunction
isomorphisms. Naturality follows directly from the open unit and reduction/pullback
comparison. Add the proof import `Sheaf.Paper.CompletedOpenEndpointLimitTransport` and
record this dependency and argument in the existing DAG node.

Existing public declarations, signatures, definitions and public imports are unchanged.

## Proved and sorry left

Closed one of the five original holes:

- `AlgebraicGeometry.Scheme.cbcRealizationReductionInv_properties`.

Four original holes remain, all attached to
`lem-cbc-complete-proetale-strict-tower-realization`:

- `AlgebraicGeometry.Scheme.cbcRealizationLimitMap_isIso`.
- `AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization`.
- `AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization_evaluation`.
- `AlgebraicGeometry.Scheme.completeProetaleStrictTowerRealization_open`.

No holes added and no statements split off. The imported endpoint theorem remains a
separate item; this delivery proves the assigned comparison from that stated dependency,
without claiming to prove the endpoint theorem itself.

## No longer needed

No original imports removed, no modules withdrawn, and no global pruning claimed.
The four remaining holes retain their existing plans and dependencies. Experimental
evaluation proofs and their unused normalization lemma are excluded from this delivery.

## Where the brief, the DAG or earlier work was wrong

The reduction comparison does not require identifying the recorded open adjunction with
the endpoint adjunction by equality. They have the same right adjoint, so uniqueness of
left adjoints supplies the canonical isomorphisms needed to transport invertibility.
`CompletedOpenStrictMateIdentification` imports this item, so importing it back to prove
the completed open clause would make a cycle. That clause remains unchanged.

The evaluation argument was explored through ordinary square normalization and the mate
cube. Its full-module checks reached the compile-time limit while comparing the derived
adjunction interfaces. No uncompiled evaluation proof is delivered.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
