## What changed

Added two named intermediate theorems to the item module: `compactificationComparison_commShift`
and `compactificationComparison_frobenius`. The target theorem `open_proper` now combines
those component results and proves its remaining naturality clause directly from
`NatTrans.naturality` of `compactificationComparison.hom`. The target statement and all
existing definitions are unchanged.

## Proved and sorry left

The naturality conjunct of `open_proper` is proved. The original `open_proper` hole is
reduced to the two strictly smaller component theorems below. The following split holes
remain, each with its own DAG node:

- `AlgebraicGeometry.NativeWeilOpenProper.compactificationComparison_commShift`
  (`lem-sf-native-weil-open-proper-forgetting-comm-shift`);
- `AlgebraicGeometry.NativeWeilOpenProper.compactificationComparison_frobenius`
  (`lem-sf-native-weil-open-proper-forgetting-frobenius`).

## No longer needed

No imports were removed. No proof-dependency nodes were pruned; the final proof now uses
the two split component nodes and naturality of the canonical comparison.

## Where the brief, the DAG or earlier work was wrong

The existing plan treated the shift compatibility and Frobenius coherence of the assembled
native compactification comparison as if they followed by immediate typeclass inference.
The current library has no direct `CommShift` instance for the canonical fixed-pair proper
comparison, and the Frobenius square expands to a nontrivial K-injective comparison diagram.
They are therefore recorded as strictly smaller named proof obligations.

## New nodes

`lem-sf-native-weil-open-proper-forgetting-comm-shift` records the shift component.
`lem-sf-native-weil-open-proper-forgetting-frobenius` records the Frobenius component.
Both are stated in the item's module with source and proof plans matching the native
comparison Steps 8--9.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.WeilSheaf.NativeOpenProperForgetting": "12686e1267f968801dd12b497996b713ba8f04ea"}, "results": {"Sheaf.WeilSheaf.NativeExceptionalHomTransport": {"hash": "b1bfb8088d3ec79a7fe43d0f8a201a0ae6d86776", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T07:59:44+0800", "transitive": 0, "version": 1}
```

## Second reading by K3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
