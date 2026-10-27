## What changed

Kept the statement, binders and public import of
`WeilConjectures.RationalVerdier.evaluation_implies_biduality` unchanged. Added a private
proof import of `RationalVerdierScalarInterchange` and a complete categorical proof:
evaluate both bidual composites, move the tensorator by naturality, use the evaluation
square twice, and cancel evaluation using its injectivity. The calculation is generic
in the two tensor bifunctors and dual functors. It does not assume the conclusion or
replace the supplied comparison with a specially chosen comparison.

Added three modules. `RationalVerdierPairingCalculus` constructs completed interchange
by conjugating the supplied ordinary signed swap with the completion maps. It proves
integral naturality and uses the existing proved raw bilinear-localization theorem to
construct the normalized natural rational swap. Its delta-evaluation calculation uses
the defining inverse-adjunction identity for IntegralVerdier.delta and completion
naturality, then explicitly transports and localizes the identity using the Datum
normalizations. `RationalVerdierEvaluationDetection` isolates injectivity of evaluation.
`RationalVerdierScalarInterchange` isolates the integral scalar signed-interchange
identity and proves the rational identity from it, using the exact pure-tensor and
component normalization formulas for the scalar functor and tensorator.

The rational tensor is used through its existing private specification API, with
proof-local transparency attributes to avoid unfolding its chosen construction.
Profiling was confined to a temporary file, which has been removed.

No existing dependency, source-library declaration, definition, instance or attribute
was changed. The item's node now describes the actual categorical calculation and
its three new dependency nodes describe the constructions and remaining obligations.
The unit record has no realized statement or step attached to this item; no unit route
is bypassed.

## Proved and sorry left

All four modules compiled in import order (the substantive pairing construction took
23.3 seconds, the scalar calculation 11.6 seconds, and the item 8.6 seconds). The final
check also verifies the unchanged original signature, the two named holes, and absence
of dependency cycles through the new nodes.

The original module had one hole, in
`WeilConjectures.RationalVerdier.evaluation_implies_biduality`. That body is now a
complete proof from the two remaining smaller assertions. The item has zero holes.
This is a decomposition, not a completed proof without additional assumptions and
not positive net sorry-ledger progress: one original hole is closed and two are added.

The delivery leaves exactly these two named theorem holes, each with a source,
complete proof in words, and matching new DAG node:

- `WeilConjectures.RationalVerdier.rational_evaluation_detect`, in
  `RationalVerdierEvaluationDetection`, node
  `lem-coef-rational-verdier-evaluation-detection`. This is only injectivity of the
  localized counit over one coefficient field. It has no scalar embedding,
  comparison, signed swap or biduality conclusion.
- `WeilConjectures.RationalVerdier.integral_scalar_interchange`, in
  `RationalVerdierScalarInterchange`, node
  `lem-coef-rational-verdier-scalar-interchange`. This is the integral completed
  tensorator/signed-swap square. It has no rationalization, evaluation-square
  hypothesis, comparison or double-dual conclusion.

The following public constructions/lemmas have complete Lean bodies:
`completedInterchange`, `PairingCalculus`, `normalized_evaluation_transpose`,
`pairing_calculus`, and `scalar_interchange`. In particular, the bidual-evaluation
formula and the passage from integral scalar interchange to rational scalar
interchange are proved here rather than included in a renamed original obligation.
The remaining detection theorem provides only a proof field of PairingCalculus;
the swap itself is explicitly constructed from the supplied normalized data.

## No longer needed

No original import was removed, and no module is withdrawn or globally pruned.
The original node's K-flat-resolution, tensor-model-rigidity and tensor-completion
steps remain needed in the new integral scalar-interchange node. The integral
Hom and raw-rationalization dependencies remain needed in the detection node and
the proved localization calculations. They have been moved to the precise steps
that need them, not declared obsolete.

The generic `EvaluationBidualComparisonTransport` module cannot directly instantiate
the arbitrary supplied tensor presentations and raw rational categories here; it is
not imported. `RationalVerdierEvaluationAdjoints` imports RationalVerdier itself and
would create a cycle; it also asserts a stronger identification with a different
closed presentation. No new duplicate of that identification is assumed.

## Where the brief, the DAG or earlier work was wrong

No false statement or assigned repair was found. The live queue lists this item as
a proof-route item; there was no current rework row or build-error file. The original
plan omits the explicit endpoint transports between the raw rational tensor objects,
the localized integral dual objects and the supplied Datum dual objects. Those are
implemented in the new proofs. The final categorical argument needs target evaluation
naturality and signed-swap naturality; it does not additionally need naturality of
the scalar dual comparison.

Edge cases were checked mathematically before writing the new statements: zero
objects and the empty scheme retain the adjunction and inverse-completion identities;
identity scalar embeddings give the same signed-swap square. The signs arise only
from complex degrees, while scalar coefficients have degree zero. No finiteness or
nonzero-object hypothesis has been added.

## New nodes

`lem-coef-rational-verdier-evaluation-detection` records nondegeneracy of the specified
localized integral counit. Its module contains the single detection theorem hole.

`lem-coef-rational-verdier-pairing-calculus` records the explicit completed interchange,
its rational natural construction, and the normalized delta-evaluation calculation.
Its module has no holes and depends on the detection node only for the injectivity
proof field. The underlying interchange data are constructed, not selected from
an unproved existence assertion.

`lem-coef-rational-verdier-scalar-interchange` records the integral degree-zero scalar
signed-swap square and its proved rationalization. Its module contains the single
integral scalar-interchange theorem hole. Neither remaining hole restates the item:
the actual comparison/evaluation-to-biduality argument is proved in the original module.

No change record is required: no other existing module or node is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierComparisonBiduality": "c2e39586fbcce4f5f39e537c4d35dd316f27549a", "Sheaf.SixFunctors.RationalVerdierEvaluationDetection": "1e1c6424667a8d091932ef740b7c299d331547a3", "Sheaf.SixFunctors.RationalVerdierPairingCalculus": "b2ecb41013c0b37a602e6682bb0e28bf16f244cc", "Sheaf.SixFunctors.RationalVerdierScalarInterchange": "2389323c4cdc6b0d9f9f4075a9656d30d40dfbe6"}, "results": {"Sheaf.SixFunctors.RationalVerdierExtension": {"hash": "eb03a68ef0c262d17b9fb672cbd50ff32a56c64c", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T07:06:19+0800", "transitive": 0, "version": 1}
```

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
