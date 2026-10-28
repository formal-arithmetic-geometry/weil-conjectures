## What changed

Repaired return of head `821a492329f` against S4's landed
`Sheaf.AlgebraicGeometry.ProperShriekCompSupportsRaw` (`20556657f`).
Retained the proof import and explicit composite-properness normalization, then
replaced the final direct application by a kernel-checked congruence transport.
The private metaprogram `compositorCongr` uses reflexivity, heterogeneous proof
irrelevance and congruence for the construction arguments. It produces an equality
between the raw equation and the required equation; `Eq.mpr` transports the proof.
No theorem statement, public import, definition, instance, or attribute changes.
All three public declarations retain their original elaboration context.
The item's node records the transport route. No change to S4's module is delivered.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.properShriekComp_comp_forgetSupports_raw_with_comp`
(node `lem-sf-proper-shriek-compositor-supports-raw-explicit`).
There are zero holes left in the item and zero added or split-off statements.
The private proof generator constructs ordinary proof terms checked by Lean's kernel.
This is a proof from the existing raw compositor theorem, not a claim to have
independently proved every theorem below that dependency.

Validation compiles the current raw source, this helper, and its unchanged direct
consumer `Sheaf.AlgebraicGeometry.ProperShriekCompSupportsCanonical`, one file at a
time in import order. The temporary byte-identical dependency/consumer copies are
removed before delivery, so only the helper, its node and this report are delivered.

## No longer needed

None. No imports, declarations, nodes, or modules are pruned. No new mathematical
helper statement is needed. The unit route and existing raw proof dependency stay.

## Where the brief, the DAG or earlier work was wrong

The single return point is repaired: the previous proof compiled against an older
raw theorem but timed out against S4's newer theorem, which gives high priority to
`DerivedCategoryModule._proof_1` and `_proof_2`. Recompiling the current raw source
then the original retained helper reproduced the 120-second timeout.
A trial aligning the helper's local instance priorities compiled the helper in
8.4 seconds, but made the unchanged consumer time out, so that trial is absent
from this delivery. The final repair preserves the original public instance
context and explicitly transports the raw equation. It identifies only proof
arguments for sheafification, Grothendieck abelianness and properness, without
unfolding the large derived-functor constructions. No limit was raised.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.AlgebraicGeometry.ProperShriekCompSupportsCanonicalHelper": "3c1e0f76cc3cbfe2a675466f4f09a21684ee6459"}, "results": {"Sheaf.AlgebraicGeometry.ProperShriekCompSupportsCanonical": {"hash": "72833df6ee278ad12cbce0a27bf9d37be0964aa5", "status": "OK"}}, "seconds": 189, "time": "2026-10-28T14:21:47+0800", "transitive": 0, "version": 1}
```

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
