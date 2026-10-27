## What changed

The main transport theorem now assembles three explicit components: source transport,
target transport, and the normalized comparison equation. These are isolated as strictly
smaller named theorem obligations in their own modules, preserving the existing public
signature whose proof-only adjunction parameters are not part of its contract.

## Proved and sorry left

Closed 1 of the original 1 sorries: `CategoryTheory.ConstantCompletion.ordinaryReducedPull_transport`.

Three lower sorries were added:

- `CategoryTheory.ConstantCompletion.ordinaryReducedPull_sourceIso`, for the source-side
  transport to the canonical finite quotient model.
- `CategoryTheory.ConstantCompletion.ordinaryReducedPull_targetIso`, for the target-side
  transport to the same model.
- `CategoryTheory.ConstantCompletion.ordinaryReducedPull_transport_eq`, for the normalized
  equality after composing the two transports.

## No longer needed

The original direct proof dependencies `lem-weil-pbc-constant-module-section-properties`
and `lem-weil-pbc-sectionwise-adic-algebra-limit` are not imported by the main proof route.
The source, target, and equation obligations retain their DAG references where their proofs
will use them; no source-library declaration was removed.

## Where the brief, the DAG or earlier work was wrong

The original one-step proof plan conflated three independent constructions: the source-side
finite comparison, the target-side scalar transport, and the normalized comparison equation.
The item contract omits the adjunction parameters needed to prove the source-side API
inline, so all three are retained as genuine lower statements rather than changing the
public theorem signature.

## New nodes

- `lem-weil-pbc-constant-completion-ordinary-reduced-pull-source-iso`
- `lem-weil-pbc-constant-completion-ordinary-reduced-pull-target-iso`
- `lem-weil-pbc-constant-completion-ordinary-reduced-pull-transport-equation`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso": "5ad848053dfc74140d66101583dd4d34fadb84eb", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso": "5eae0dbffbd809cc88de06396fb481444dae3ff0", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport": "c14d32960fead148af9e9353bdacbca8c8160d0c", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransportEquation": "b03c50985deafc6d83ff42627b8486802396a8c7"}, "results": {}, "time": "2026-10-28T05:19:54+0800", "transitive": 0, "version": 1}
```

## Second reading by P3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
