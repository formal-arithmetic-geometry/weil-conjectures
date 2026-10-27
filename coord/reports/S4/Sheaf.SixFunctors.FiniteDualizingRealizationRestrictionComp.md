## What changed

Proved `WeilConjectures.finiteDualizingRealizationRestriction_comp` by unfolding the
realization restriction square and composing two strictly lower coherence statements.
Added `FiniteDualizingIntrinsicRestrictionComp` for intrinsic normalized restriction
composition and `FiniteDualizingRestrictionTransport` for transport through the
comparison-site square. The target imports these proof dependencies privately.

## Proved and sorry left

The target theorem `finiteDualizingRealizationRestriction_comp` is proved. Two strictly
simpler decomposition statements remain as named sorries:
`finiteDualizingIntrinsicRestriction_comp` (`lem-coef-dualizing-intrinsic-restriction-comp`)
and `finiteDualizingRealizationRestriction_transport`
(`lem-coef-dualizing-realization-restriction-transport`). No definition contains a
`sorry`.

## No longer needed

No declared dependency was pruned. The target uses finite dualizing data, normalized DVR
restriction, witness compatibility, and the two new lower coherence statements.

## Where the brief, the DAG or earlier work was wrong

The earlier split supplied the target as a lower coherence node but no Lean theorem for
its two independent layers. The target can be reduced cleanly to intrinsic composition
and comparison transport; both are recorded as new nodes rather than repeating the
whole target obligation.

## New nodes

`lem-coef-dualizing-intrinsic-restriction-comp` states the intrinsic section-normalized
restriction compositor identity and is realized by
`Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionComp`.

`lem-coef-dualizing-realization-restriction-transport` states the comparison-site
transport identity after intrinsic composition and is realized by
`Sheaf.SixFunctors.FiniteDualizingRestrictionTransport`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingIntrinsicRestrictionComp": "9405cae69a2299bea40a55b73854621d9c095e75", "Sheaf.SixFunctors.FiniteDualizingRealizationRestrictionComp": "f5040b45b9503f0a66217cd4212a2b41040d48c9", "Sheaf.SixFunctors.FiniteDualizingRestrictionTransport": "a706aac77aea480e2a7af677ef6b4e1c5eeae4a8"}, "results": {}, "time": "2026-10-28T06:58:51+0800", "transitive": 0, "version": 1}
```

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
