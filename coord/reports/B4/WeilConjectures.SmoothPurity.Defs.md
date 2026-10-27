## What changed

Closed `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion`.
The proof adds a private generic adjunction lemma showing that the counit composite
through an isomorphism is a representing pairing. It applies the existing unique
representing-trace theorem to identify the chosen `smoothTrace` for an open immersion,
then invokes the existing reconstructed-trace normalization lemma.

## Proved and sorry left

Closed one sorry:
`AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_zero_of_isOpenImmersion`.

Two pre-existing sorries remain unchanged:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_smoothPurityMap`, whose elaborated
  unconditional signature is statement-disputed in the source module;
- `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityIso_comp_openImmersion`.

No new sorry was added.

## No longer needed

No imports or DAG dependencies were pruned. The existing representing-trace and
reconstructed-trace route remains needed.

## Where the brief, the DAG or earlier work was wrong

The unconditional `isIso_smoothPurityMap` instance remains statement-disputed as
already documented in the module: the identity of a separably closed point with a
proposed positive relative dimension gives a counterexample. The completed proof
avoids that disputed instance and uses only adjunction, the unique representing-trace
property, and the existing reconstructed-trace formula.

## New nodes

None.

## Related modules compiled before delivery

4 related module(s) compiled against this delivery by deliver3.py: 4 OK.

```json
{"capped": false, "direct": 4, "left_out": 0, "own": {"WeilConjectures.SmoothPurity.Defs": "bf5789f90d911ab0a7e6484aa9e6fa239ca04954"}, "results": {"Sheaf.Targets.SmoothPurityQbar": {"hash": "b61095f4237cc889a88d12105bb9497ef53983af", "status": "OK"}, "WeilConjectures": {"hash": "29212a36c63202a1e8f818f492570e5df8885134", "status": "OK"}, "WeilConjectures.PoincareDuality.Poincare": {"hash": "24c41d940617dccc117d662fe9a0ea621d946970", "status": "OK"}, "WeilConjectures.TraceFormula.Dualizing": {"hash": "6f0205d1db4c599fd319656d4acc1446b3c84ebb", "status": "OK"}}, "seconds": 78, "time": "2026-10-28T07:23:00+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
