## What changed

Proved `AlgebraicGeometry.Etale.etaleScalarPullback_tensor` by expressing both sides as
natural transformations between uncurried tensor functors. A flat K-flat resolution
extensionality lemma reduces equality of these transformations to representative pairs.
The representative calculation is isolated in
`AlgebraicGeometry.Etale.etaleScalarPullback_tensor_kFlat`.

## Proved and sorry left

Closed the original sorry in `etaleScalarPullback_tensor`. One strictly smaller
representative theorem was split off and remains sorry:
`etaleScalarPullback_tensor_kFlat` in
`Sheaf.Paper.EtaleScalarPullbackTensorKFlat`.

## No longer needed

None. The proof uses only `ExceptionalCoefficientMaps`, the flat K-flat resolution
interface, and the new representative statement; no planned dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The DAG described the representative calculation as an inline step. Lean's derived
tensor functors require an explicit uncurrying natural transformation and a separate
flat K-flat representative statement, so that step is recorded as the new node below.
No target statement or existing public declaration was changed.

## New nodes

* `lem-pur-etale-scalar-pullback-tensor-kflat-representative`, implemented by
  `Sheaf.Paper.EtaleScalarPullbackTensorKFlat`.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 3 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.EtaleScalarPullbackTensorCoherence": "2ee355c371d5d1a32f81d34a5f10ed1475680336", "Sheaf.Paper.EtaleScalarPullbackTensorKFlat": "e9f2154affb1293be6635cd94af812eb35ac0c0b"}, "results": {"Sheaf.Paper.EtaleDirectScalarProjection": {"hash": "21d4d2509f5bea37b99e350ad0d0573056608c5d", "status": "OK"}, "Sheaf.Paper.EtaleScalarPullbackUnitCoherence": {"hash": "9e51a8c4b243bd30cff319918d62384acad81c64", "status": "OK"}, "Sheaf.SixFunctors.EtaleOpenScalarRestrictionTensor": {"hash": "a8752c02bd02a09b72042fc4752ea3bad13eca0f", "status": "OK"}}, "seconds": 60, "time": "2026-10-28T03:56:25+0800", "transitive": 0, "version": 1}
```

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
