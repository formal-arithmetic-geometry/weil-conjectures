## What changed

The assigned theorem now composes two explicit proof-plan lemmas. The first split-off module states the closed-boundary restriction vanishing for the intrinsic extension by zero. The second split-off module states the remaining proper-boundary cohomology argument from that restriction vanishing. The assigned module imports both proof-only modules and applies them in order. The original theorem statement and the injective-resolution instance are unchanged.

## Proved and sorry left

The assigned declaration AlgebraicGeometry.Scheme.proEtale_proper_boundary_cohomology is closed by a real application of the two split-off declarations. Two strictly lower proof obligations remain as named theorems:

- AlgebraicGeometry.Scheme.proEtale_proper_boundary_extension_restricts_zero (node lem-sp-proetale-proper-boundary-closed-restriction), whose proof is the disjoint closed-boundary restriction step.
- AlgebraicGeometry.Scheme.proEtale_proper_boundary_cohomology_of_closed_restriction_zero (node lem-sp-proetale-proper-boundary-from-closed-restriction), whose proof is the proper-base-change, open-closed localization, specialization-zero, and weakly-contractible evaluation steps.

No sorry remains in a definition.

## No longer needed

No existing proof-dependency node was pruned. The split follows the seven-step route in the item docstring; all original imports remain available. The new proof-only imports are the two split-off modules listed above.

## Where the brief, the DAG or earlier work was wrong

The original module's full proof is substantially longer than the available interface permits in one declaration. The DAG's seven-step route omits named Lean interfaces for the closed-boundary restriction and for the final global evaluation argument. Those two strictly simpler obligations are now represented explicitly as new nodes instead of being hidden inside the target proof.

## New nodes

lem-sp-proetale-proper-boundary-closed-restriction is the base-change/open-closed restriction statement used by step 2.

lem-sp-proetale-proper-boundary-from-closed-restriction is the remaining global cohomology statement used by steps 3--7, with the closed-restriction vanishing supplied as an explicit hypothesis.


## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryClosedRestriction": "e8e84f1442f8b5d62f9c7d21a48061a6ea2b6704", "Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomology": "35810bab9669c3759e9b5f7bda955e7acc17b788", "Sheaf.AlgebraicGeometry.ProEtaleProperBoundaryCohomologyOfClosedRestriction": "d175425d4d7df7d78539e2c070c37680b128c33b"}, "results": {}, "time": "2026-10-28T06:34:44+0800", "transitive": 0, "version": 1}
```

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
