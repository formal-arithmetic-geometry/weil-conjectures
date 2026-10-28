## What changed

Proved `WeilConjectures.canonicalRationalPullbackTensorComposition_right_localization`
in `Sheaf.Paper.CanonicalRationalPullbackTensorCompositionRightLocalization` with its
statement unchanged. The proof uses the existing object equations, normalized compositor
and comparison hom equations, and the scalar-one pullback map equation. Two applications
of `CategoryTheory.heq_comp` assemble the three factors; `Functor.map_comp` identifies
the resulting composite with localization of the integral composite.

Updated the item's node proof, proof dependencies, and proof origin to record these
actual steps and the current owning nodes after earlier module extractions. No imports,
definitions, public signatures, instances, or attributes changed. No other module changed.
The current queue row is `proof / route`; there is no rework row or build-error file for
this item, including in the current server records.

Single-file verification with `lcompile.py` passed without warnings in 5.4 seconds.
The existing module import supplies every declaration used; no new import is needed.
The unit's route is preserved. No new statements or hypotheses were introduced.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.canonicalRationalPullbackTensorComposition_right_localization`
(node `lem-pur-pullback-tensor-rational-composition-coherence-right-localization`).

There are zero remaining holes in the item, zero holes added, and zero split-off
statements. The proof uses existing normalization theorems rather than adding obligations.

## No longer needed

No Lean imports removed and no module pruned. The earlier proof-dependency owner nodes
`def-weil-derived-pullback-tensor-hom` and
`def-pur-completed-pullback-tensor-comparison` are replaced in this node's proof edges by
the current owners `def-sf-finite-rational-derived-operations` and
`def-pur-completed-pullback-tensor-construction`. This records the extraction already
present in the library, without claiming either older module is globally unnecessary.
The compositor specification is explicitly recorded through
`lem-pur-derived-pullback-tensor-constraints`.

## Where the brief, the DAG or earlier work was wrong

The one-step plan is mathematically sufficient: its endpoint transports can be proved
from the existing object formulas, and the pullback map formula at scalar one handles
the middle factor. No further split is needed. The earlier dependency list named the
pre-extraction owners and did not explicitly list the compositor's constraint node;
the updated proof dependencies identify the declarations actually used.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CanonicalRationalPullbackTensorCompositionRightLocalization": "4722ee032a97965840a8547ba8eb07f117b6a17f"}, "results": {}, "time": "2026-10-28T07:47:33+0800", "transitive": 0, "version": 1}
```

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
