## What changed

Filled the parent theorem's naturality, kappa invertibility, and constructibility clauses directly from the natural transformation and existing preservation lemmas. Added the named intermediate theorem `integralPointTransportTowerPowers_remaining` for the remaining power, finite evaluation, realization, naturality, compositor, Frobenius normalization, and reduction identities.

## Proved and sorry left

Proved `WeilConjectures.integralPointTransportTowerPowers` by assembling the direct clauses and the intermediate result. Closed the naturality, kappa-isomorphism, and pullback-constructibility clauses. One sorry remains in `WeilConjectures.integralPointTransportTowerPowers_remaining`; it is a strict conjunction of the unresolved clauses and has node `lem-trf-integral-point-transport-tower-powers-remaining`.

## No longer needed

No imports or declared dependencies were removed. The direct proof uses the transport naturality field, `kappa_isIso`, and `integralOperations_preserve_constructible`.

## Where the brief, the DAG or earlier work was wrong

The existing module's global build record reported bad imports even though the current published dependency artifacts compile the module. The proof plan contains several whole-system identities that cannot be discharged from the declarations currently available; they were retained as one named strict intermediate conjunction rather than left as an anonymous partial proof.

## New nodes

`lem-trf-integral-point-transport-tower-powers-remaining` records the remaining whole-system identities and their blueprint assembly source.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.IntegralPointTransportTowerPowers": "ed2428697f027f00e3c16fe4f2f75c50d4a8493b"}, "results": {"Sheaf.Paper.CompactSupportSystemRealizationNormalization": {"hash": "3d61967d7537aa959d68b7f6983cffadfe893a0e", "status": "OK"}, "Sheaf.Paper.ConstantExtensionReturnData": {"hash": "d5790776d99d2f250460dcecb2d299f9aae9a972", "status": "OK"}, "Sheaf.TraceFormula.LocalNormalizationStrictRealization": {"hash": "d80b1639021816dcdad1dc32e586a5d79de75bb7", "status": "OK"}}, "seconds": 103, "time": "2026-10-28T07:29:16+0800", "transitive": 0, "version": 1}
```

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
