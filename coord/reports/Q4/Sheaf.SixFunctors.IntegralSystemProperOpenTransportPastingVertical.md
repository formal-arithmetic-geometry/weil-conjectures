## What changed

Repaired the missing canonical-normalization hypothesis in
`integralSystemProperOpenTransportPastingVertical` and in its package caller,
`integralSystemProperOpenTransportPasting`. The unchanged existence theorem
`integralSystemProperOpenTransport` supplies the bridge and `hc.canonical` from its
existing core. The new proof dependency `IntegralSystemBridgePushComposition`
compares the specified pushforward compositors, independently of gamma.

The change record is
`coord/changes/Q4-integral-proper-open-vertical-normalization.md`.
Both existing consumer modules were checked as unclaimed on the current server.
No existing definitions or instances, public imports or target signatures change.

## Proved and sorry left

The original one-hole declaration
`integralSystemProperOpenTransportPastingVertical` is replaced by its source-correct
canonical statement and a complete proof. The former unrestricted assertion is false;
this delivery does not claim to prove that assertion. The repaired theorem uses the
fully proved new `integralSystemBridgePushComposition`, with proved private conjugation,
localization, section-comparison and categorical transport calculations.

Original hole count: 1. Repaired declaration hole count: 0. Added hole count: 0.
No `sorry` remains in any delivered Lean file. This is a statement
repair together with a proof of the repaired theorem, rather than a decomposition.
The existing transport theorem's statement and the pasting record type stay identical.
All five delivered modules compiled in import order through `lcompile.py`: ordinary
comparison 25.9 s, derived comparison 29.1 s, vertical transport 17.3 s, package 11.9 s,
and its existence-theorem caller 4.2 s. A subsequent `#print axioms` check found only
`propext`, `Classical.choice` and `Quot.sound` for both the derived comparison and
vertical transport. The diagnostic commands have been removed. The unused open
comparison parameter is retained as `_a` in the vertical theorem.

## No longer needed

None. All original declared dependencies remain needed. No source-library declaration
or unit step is pruned. The new compositor comparison addresses the missing
identification in the existing plan; it does not rename or repeat the pasting goal.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (original signature): the original theorem claimed coherence for
every supplied natural transformation without a bridge equation. Its parent already recorded this as STATEMENT-DISPUTED.
On an identity diagram, scaling the canonical map by a non-idempotent scalar shows
why the claimed equation cannot follow. The correction follows the source's canonical
transport construction. The old and new statements and full citer audits are in the
two updated nodes' statement_change records. The sole direct node citer of the vertical
node is the pasting package, repaired here. The sole direct node citer of the package
is the transport theorem, which already has the required canonical core and is adapted
here without a statement change. The horizontal and base-change components have the
same overly general signatures; this delivery does not change their owners' files.

## New nodes

`lem-sf-integral-system-bridge-push-composition` owns
`Sheaf.SixFunctors.IntegralSystemBridgePushComposition` and
`integralSystemBridgePushComposition`. Its statement concerns only two composable
pushforward functors and their bridge comparisons, for arbitrary scheme maps; no
proper/open gamma or pasting equation occurs. Its proof conjugates the proved ordinary
comparison, localizes and conjugates again.

`lem-sf-integral-system-ordinary-bridge-composition` owns
`Sheaf.SixFunctors.IntegralSystemOrdinaryBridgeComposition` and
`integralSystemOrdinaryBridgeComposition`. It compares ordinary direct-image
compositors by their section formulas. Both new modules are fully proved. Separating
ordinary and derived comparison keeps their single-file compilation below the limit
after local irreducibility annotations and focused rewriting removed expensive unfolding.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.IntegralSystemBridgePushComposition": "6649b034c83ab68f39a6f484f5dfd285cf34e168", "Sheaf.SixFunctors.IntegralSystemOrdinaryBridgeComposition": "cb143637c492e1dc1b3db1e2f0bba95f30d61955", "Sheaf.SixFunctors.IntegralSystemProperOpenTransport": "6e59ff1c5dbf92115c62a68ceab701cb0815d60c", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportPasting": "ea32850099fb1b0de3557d215166c621333c28f8", "Sheaf.SixFunctors.IntegralSystemProperOpenTransportPastingVertical": "39ca223a4662e65c1dac515de65effd6dd882e0f"}, "results": {}, "time": "2026-10-28T11:30:01+0800", "transitive": 0, "version": 1}
```

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
