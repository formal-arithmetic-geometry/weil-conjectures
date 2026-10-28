## What changed

Proved `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.finite_formula_unit_exists`
in `Sheaf.Paper.IsomorphismScalarFiniteComparisonUnit`. All auxiliary constructions
and proofs are private to this module. No existing statement or definition changes.

The proof identifies the three concrete ordinary extension functors with the existing
sheafified scalar extension using their object and map presentations. Naturality of
the finite coefficient comparison gives the restriction square. Its adjunction mate
is invertible because sectionwise inverse image is an equivalence. Compose that mate
with scalar-extension reassociation and the presentation identifications, compute its
rule on double pure tensors, lift termwise to complexes, and restrict to good complexes.
The last step sets the middle coefficient to 1.

Replaced the public import of `IsomorphismScalarCompletedModel` with
`IsomorphismScalarCompletedModelBase`, which supplies the vocabulary used by the
unchanged statements. Proof-only imports expose the existing helpers in
`IsomorphismScalarQuotientChainSquares`, `IntegralReductionTowerUnrestricted`, and
`InverseImagePullbackComparison`; their declarations and interfaces are unchanged.
The item's DAG proof records this concrete argument.

Validation: the final single-file compile passed without warnings in 50.3 seconds,
within the unchanged 60-second limit. The delivered module contains zero `sorry`
tokens; all profiling options have been removed.

## Proved and sorry left

Closed 1 existing hole:
`AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.finite_formula_unit_exists`
(node `lem-weil-isomorphism-scalar-finite-comparison-formula-unit`).
No holes added, no split-off statements, and no `sorry` remains in the delivered module.
The private helpers are all proved. Existing dependencies retain their own obligations.

## No longer needed

Removed the direct import `Sheaf.Paper.IsomorphismScalarCompletedModel`; its
completed-comparison and model-preservation proofs are not used here. The
replacement `IsomorphismScalarCompletedModelBase` retains the definitions needed
by the statements. Other consumers still import the completed-model theorems, so
no whole-library module withdrawal is claimed. No declared proof dependency is
pruned. The finite construction does not use the
supplied completed comparison `b` or its normalization `hb`; it is constructed
independently from the finite coefficient maps. Their hypotheses and the public
statement remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The old proof sketch did not spell out the comparison between the concrete chosen
ordinary-extension presentations and the canonical scalar-extension functor. Those
identifications follow from their prescribed object and map equalities; no new
existence theorem or new hole is needed. The finite isomorphism also does not need
the completed comparison, contrary to the old description that obtains it from the
completed normalization. The unit's route is preserved.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarFiniteComparisonUnit": "68ca23db7ca4c1a1e0ae684bceb7ce3d8c9c5ce4"}, "results": {"Sheaf.Paper.IsomorphismScalarFiniteComparisonExtension": {"hash": "991e1f8dbc18672728fbe44a766a492bec6ab242", "status": "OK"}}, "seconds": 67, "time": "2026-10-28T10:32:01+0800", "transitive": 0, "version": 1}
```

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
