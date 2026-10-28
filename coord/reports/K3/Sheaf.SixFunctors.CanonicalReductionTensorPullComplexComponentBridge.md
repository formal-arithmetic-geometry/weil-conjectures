## What changed

Proved `WeilConjectures.IntegralSystemRealization.canonicalReductionTensorPullComplex_component_bridge`
with its statement unchanged. All Lean changes are in the assigned module.
Private helpers project the actual reduction unit, prove its naturality and tensor-generator law,
compute the canonical mate on successive units, and reduce equality to total tensor generators
through the two adjunctions. The final proof compares these generators on both routes.

Validation: the final assigned module compiles cleanly through `lcompile.py`
in 42.9 seconds, with the original theorem signature byte-for-byte unchanged.
No profiling options or extra heartbeat limit are present in the delivered module.

Added proof imports of `Sheaf.SixFunctors.PullQuotientOrdinaryProjectionSection`,
`Sheaf.Algebra.Homology.ScalarHomTensorCoherence` (its proved private tensor extensionality
and tensor-map formulas), and `Sheaf.Paper.ProEtaleTotalTensorPullbackGenerators`.
The last two modules were already in the item's import closure. The additional projection
module contains no `sorry`. Updated the node's proof, proof dependencies and proof origin.

## Proved and sorry left

Closed the one original hole in
`WeilConjectures.IntegralSystemRealization.canonicalReductionTensorPullComplex_component_bridge`
(node `lem-sf-canonical-reduction-tensor-pull-complex-component-bridge`).
Holes closed: 1. Holes added: 0. Remaining holes in this delivery: 0. No split-off statements.

## No longer needed

The proof does not use the planned dependency
`lem-sf-scalar-pull-coefficient-total-tensor` / `Sheaf.Paper.ScalarPullCoefficientTotalTensor`.
The direct unit-generator computation replaces that coefficient-square transport.
Removed this node from `proof_deps`; the inherited `stmt_deps` is unchanged.
No existing import was removed, and no module is withdrawn or claimed globally unused.

## Where the brief, the DAG or earlier work was wrong

The original two-step plan hides the reduction unit formula and the ordinary mate's unit
formula. Both can be proved from the existing normalization APIs, so another split is unnecessary.
The proof uses the private projection API already proved in
`PullQuotientOrdinaryProjectionSection`, rather than rebuilding the finite scalar/pullback
coefficient square. No target statement, shared definition, instance, public import or public attribute changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponentBridge": "a8c9316ef07bd7e02ba16f4a9962e5ea52dd8ce1"}, "results": {"Sheaf.SixFunctors.CanonicalReductionTensorPullComplexComponent": {"hash": "9f57bfb8bae0db65bdfdde519cfc0a3e05f46c7f", "status": "OK"}}, "seconds": 75, "time": "2026-10-28T10:40:55+0800", "transitive": 0, "version": 1}
```

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
