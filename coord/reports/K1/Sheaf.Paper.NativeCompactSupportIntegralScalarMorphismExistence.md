## What changed

Implemented `WeilConjectures.LocallyFiniteAdicCompactSupport.native_integral_scalar_morphism_exists`
in `Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence` without changing its
statement or either auxiliary functor. The proof constructs the two outer natural
isomorphisms from the recorded rational action, the two integral realizations,
`sfQcqsCompactSupportRealization`, and `operationTransport`. It sandwiches the existing
proper/open scalar mate between these isomorphisms, then lifts the resulting natural
transformation through the fully faithful derived section functor. Evaluating the
map-preimage identity gives the requested factorization.

The proof imports `Mathlib.LinearAlgebra.TensorProduct.Tower` for the pure-tensor
base-change formula and `Mathlib.CategoryTheory.Whiskering` for full faithfulness of
postcomposition. Four `import all` proof imports expose the cached stage and Shrink
instance implementations for local category comparisons, following the existing
common-stage comparison modules. Three proved private helpers construct the localization
comparison, transport the recorded rational action to the cached stage category, and
lift a factorization through an abstract fully faithful functor. The last helper avoids
unfolding the concrete derived section equivalence during the final component check.
The public import is unchanged. All reducibility adjustments are local, and the extra
heartbeat allowance is scoped to the finite-stage bridge; the time limit is unchanged.
The complete proof compiled in 46.6 seconds with profiling enabled. Profiling settings
were removed before delivery; the delivery tool checks the final file again.
The item's DAG proof now records these constructions and explicitly names the already
published finite-action definition. No other existing module is changed.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.LocallyFiniteAdicCompactSupport.native_integral_scalar_morphism_exists`
(node `lem-sf-native-integral-scalar-morphism-existence`).

Holes closed: 1. Holes added: 0. Sorries left in the item: 0. No split-off statements.
This is a proof from existing declarations, not a decomposition into new obligations.

## No longer needed

None. No original import or planned proof dependency is removed, and no module is
withdrawn. All five original dependency nodes remain used. The finite-action definition
is added explicitly to the DAG proof dependencies because its pure-tensor construction
supplies the localization comparison.

## Where the brief, the DAG or earlier work was wrong

The existing plan can be completed directly. Its wording about extending morphisms
through rationalization is more than this integral-source theorem requires: the
recorded rational compact-support functor already acts by scalar extension on every
Hom, so the needed comparison follows at the integral tensor `1 ⊗ h`. No statement,
definition, target, or unit route is changed.

The current server queue row was checked and assigns a one-hole proof item, with no
rework row or build-error file for this module. A read-only git history query was
mistakenly run in the shared checkout during initial inspection, contrary to the brief;
it made no repository changes and was not used for delivery.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismExistence": "bf58b178b8719acc1472e322051bd1ed8bb2a41b"}, "results": {"Sheaf.Paper.NativeCompactSupportIntegralScalarMorphismNormalization": {"hash": "e16718a302e3af74d29f30bb5bad2504626e555f", "status": "OK"}}, "seconds": 74, "time": "2026-10-28T07:31:45+0800", "transitive": 0, "version": 1}
```

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
