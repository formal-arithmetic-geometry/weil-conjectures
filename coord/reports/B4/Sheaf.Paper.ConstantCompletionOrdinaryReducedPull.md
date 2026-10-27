## What changed

Added `Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport`, which isolates the
finite ordinary transport/conjugacy assertion.  The assigned theorem now obtains the
common finite-module functor and cancels its target isomorphism; its declaration and
hypotheses are unchanged.

## Proved and sorry left

`CategoryTheory.ConstantCompletion.ordinaryReducedPull_isIso` is proved by categorical
cancellation.  The new declaration
`CategoryTheory.ConstantCompletion.ordinaryReducedPull_transport` remains a named
split-off theorem with one `sorry` (node
`lem-weil-pbc-constant-completion-ordinary-reduced-pull-transport`).

## No longer needed

The original direct imports for the sectionwise and geometric transport lemmas are not
needed by the assigned module after the transport assertion is isolated; the assigned
module imports only `ConstantCompletionDerivedPull` and the transport module.

## Where the brief, the DAG or earlier work was wrong

The original proof plan omitted the concrete ring-category transport between the
abstract common-quotient presentation and the prescribed constant-completion functors.
The missing step is now stated explicitly as the transport node; the final cancellation
is independent of those presentation details.

## New nodes

`lem-weil-pbc-constant-completion-ordinary-reduced-pull-transport` states the common
finite-module transport and normalized conjugacy equation used by the assigned proof.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryReducedPull": "71de0f0b4e43f0db773f503cde642178994e49f7", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport": "be489a11df74241eb3a270fe84d1e72dd3ba2a58"}, "results": {}, "time": "2026-10-28T02:44:33+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
