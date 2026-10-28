## What changed

Proved `CategoryTheory.ConstantCompletion.ordinaryReducedPull_sourceIso` by taking
`ordinaryFinitePull_existsUnique`, whiskering its isomorphism on the left by
restriction of scalars, and composing with `finiteComparison` whiskered on the
right by finite-coefficient pullback. This is the existing DAG plan; no new
intermediate statement or Lean module is needed. No imports changed.

Restored explicit V, adj : L ⊣ V, and PreservesFiniteLimits L hypotheses to the
source theorem and its transport caller. Adapted the unclaimed
ConstantCompletionOrdinaryReducedPullTransport and
ConstantCompletionOrdinaryReducedPull modules to pass that context. The outer
ordinaryReducedPull_isIso signature is unchanged. Updated the source node's
statement/correction record and both changed theorem Lean attachments.

Change record: coord/changes/D6-ordinary-reduced-pull-geometric-context.md.

Validation: lcompile --all compiled the source, TargetIso, TransportEquation,
transport, ordinary reduced pull, and CompletedFinitePull separately in import
order, with no errors or warnings (2.2, 1.6, 2.2, 2.3, 2.0, and 4.4 seconds).
The three unchanged validation copies were removed before delivery. The proof
uses only categorical isomorphism composition; I = 0, I = A, n = 0 and the zero
ring require no exceptional argument or new nontriviality hypothesis.

## Proved and sorry left

Closed the sole hole of the corrected
`CategoryTheory.ConstantCompletion.ordinaryReducedPull_sourceIso`
(node lem-weil-pbc-constant-completion-ordinary-reduced-pull-source-iso).
The item has zero sorry left. Added zero holes and split off zero statements.
Both adapted consumer modules remain free of direct sorry. This is a proof with
a necessary repair of omitted geometric hypotheses, not a proof of the false
original generality and not a decomposition.

## No longer needed

None. The existing plan uses both the normalized ordinary finite pullback
comparison and the normalized finite coefficient comparison. No import, node,
module or unit step is pruned.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (original interface, repaired here): unused section variables
V, adj, and finite-limit preservation were not part of sourceIso or transport.
The parent node for transport and the outer ordinaryReducedPull_isIso already
require a geometric inverse image. Stacks 03EL likewise assumes a morphism of
ringed topoi and explicitly uses its inverse/direct-image adjunction.

Without that context the source assertion is false. Let L take invariants of
C2-actions, with the natural algebraic lifts and identity constant-ring
comparison. This preserves finite limits. For A = ℤ, I = (2), n = 0 and the
completed module ℤ₂ with sign action, the left functor yields zero and the
right functor yields ℤ/2. The corrected signatures restore the source's intended
hypotheses rather than changing a target or bypassing a unit step.

The singleton source citer audit is recorded in statement_change: transport
already assumes this context in words, and the corrected Lean interface retains
it. Its caller already has the required adjunction. No held module is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.ConstantCompletionOrdinaryReducedPull": "721d3428bae1b5bf3bc6f56d0c4d935c02b7fe37", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullSourceIso": "c48124d6baf3e6ebe8b632802b8b6ebf6a5f3a57", "Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTransport": "dd73684a20ab3c433e767d966ec4a4689a8ee129"}, "results": {"Sheaf.Paper.ConstantCompletionOrdinaryReducedPullTargetIso": {"hash": "5eae0dbffbd809cc88de06396fb481444dae3ff0", "status": "OK"}}, "seconds": 77, "time": "2026-10-28T07:57:04+0800", "transitive": 0, "version": 1}
```

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
