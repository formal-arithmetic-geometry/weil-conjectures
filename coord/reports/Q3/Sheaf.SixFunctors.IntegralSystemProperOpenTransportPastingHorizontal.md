## What changed

Corrected integralSystemProperOpenTransportPastingHorizontal to require the canonical
bridge and its gamma component equation. The existing assembly theorem already has
these premises; its horizontal field now passes them. Its signature and the final
transport theorem stay unchanged. The proof packages actual intrinsic functors and
bridge isomorphisms in private structures, then applies the proved categorical
naturality and cancellation calculation horizontalMateTransport. The binary open
bridge is proved by conjugating the already proved pullback-compositor bridge.

## Proved and sorry left

The original item has one hole in
WeilConjectures.IntegralSystemRealization.integralSystemProperOpenTransportPastingHorizontal.
Its unrestricted statement is false and is explicitly corrected, rather than claimed
proved verbatim. The corrected theorem has a complete proof. No sorry remains in the
item and none is added. Both new support theorems, horizontalMateTransport and
integralSystemOpenCompositorBridge, are proved. No existing dependency holes change.

## No longer needed

No existing module or DAG node is pruned. All three originally declared dependencies
remain used, through the statement interface or intrinsic pasting. The retained proof
uses no presentation-wrapper modules from the earlier unfinished sandbox work; those
were never part of the library. The original public import is preserved. New proof
imports are private. No adopted source declaration or public import is changed.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (repaired): arbitrary gamma need not satisfy a law linear in the
outer gamma and quadratic in the two inner gammas. Negate the canonical nonzero mate
on identity squares with coefficients where 2 is nonzero: the signs disagree.
Stacks more-etale, lemma-shriek-proper-and-open-compose-horizontal, proves the law
for the canonical mate. The current parent already supplies its bridge normalization,
following the vertical repair. This delivery only threads those existing assumptions
into its horizontal field. Its sole DAG citer still holds under its present premises;
the statement_change audit and change record say so. The unit route is preserved.
The earlier sandbox report and change record predated the vertical repair and have
been rebased to the current source. Exploratory files were moved outside lean/.

## New nodes

lem-sf-horizontal-mate-transport records the proved categorical transport calculation.
It assumes five comparison squares, cancels an endpoint isomorphism and uses
naturality to reduce horizontal pasting to the intrinsic equation.

lem-sf-integral-system-open-compositor-bridge records the proved binary open-compositor
compatibility. It conjugates pull_bridge_composition through the three open
adjunctions, using conjugate_composition_injective, bridge_conjugate, and
conjugate_leftAdjointComp. This has no proper/open gamma premise and is a strictly
smaller input to horizontal transport. Identity and empty opens require no extra
hypotheses. The change record is
coord/changes/Q3-horizontal-transport-normalization.md.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.HorizontalMateTransport": "d46733579f9b36f6ee3dcd9e1f3fd25d0d2340bc", "Sheaf.SixFunctors.IntegralSystemOpenCompositorBridge": "d733bd9fa5eb8d50994a33df8bb437235f9185b6", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportPasting": "a6276b041a36f5308098b509f4eba723d051ecac", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingHorizontal": "c0bda5d1bac5eac9173b19fef89d103103b91ff5"}, "results": {}, "time": "2026-10-28T14:59:45+0800", "transitive": 0, "version": 1}
```

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
