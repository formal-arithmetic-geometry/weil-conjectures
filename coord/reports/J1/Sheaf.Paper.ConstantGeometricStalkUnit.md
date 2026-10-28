## What changed

Restored the reviewed compile-time extraction for the constant coefficient-unit block.
`Sheaf.Paper.CoefficientPullbackUnitCoordinates` contains the finite and completed
coefficient constructions and proves `integralChainUnit_isIso` through the fully proved
`Sheaf.Paper.ConstantPullbackUnitQuasiIsomorphism` helper. The assigned module publicly
re-exports that block, preserving all original declaration names and signatures. The
quasi-isomorphism helper proves the normalized arbitrary-morphism Roos unit by the actual
finite tower, limit cone, and Milnor comparison.

The packet adds the two proved helper modules and their DAG nodes, and updates the item
node to record the extracted implementation. No target statement or public declaration
signature changes.

## Proved and sorry left

Closed one of the four original holes:

- `WeilConjectures.ConstantGeometricStalkUnit.integralChainUnit_isIso`.

The following three original holes remain, with their existing complete proof
specifications and DAG ownership:

- `WeilConjectures.ConstantGeometricStalkUnit.finiteOperator_unit`;
- `WeilConjectures.ConstantGeometricStalkUnit.integralOperator_unit`;
- `WeilConjectures.ConstantGeometricStalkUnit.rationalOperator_scalar`.

No new `sorry` declarations were added. The two added modules compile with zero
`sorry`s.

## No longer needed

The assigned module no longer directly contains the extracted coefficient-unit proof
imports; they are private/public imports of `CoefficientPullbackUnitCoordinates`, where
their declarations are used. No unit-level route or mathematical dependency is
withdrawn. The new helper node is the proof dependency for the closed integral-chain
hole.

## Where the brief, the DAG or earlier work was wrong

The combined module exceeded the fixed file compile limit because the self-contained
coefficient-unit construction and the arbitrary-map Roos quasi-isomorphism were
elaborated together. The reviewed extraction keeps the same declarations, data, and
proof route while compiling each module within the limit. The remaining three operator
holes are unchanged.

## New nodes

`lem-zl-constant-pullback-unit-quasi-isomorphism` records the proved normalized
arbitrary-morphism Roos-unit quasi-isomorphism in
`Sheaf.Paper.ConstantPullbackUnitQuasiIsomorphism`.

`lem-zl-coefficient-pullback-unit-coordinates` records the extracted finite and
completed coefficient-unit declarations, including the proved
`integralChainUnit_isIso`, in `Sheaf.Paper.CoefficientPullbackUnitCoordinates`.

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 4 OK, 1 SLOW.

```json
{"capped": false, "direct": 5, "left_out": 0, "own": {"Sheaf.Paper.CoefficientPullbackUnitCoordinates": "9514ad26809e4537549d2b5655a885ac0451486a", "Sheaf.Paper.ConstantGeometricStalkUnit": "bb9a9d8ce410d1e57b358ae2fab39513e50b05e7", "Sheaf.Paper.ConstantPullbackUnitQuasiIsomorphism": "c4ee9d6ac15399631d42d20c79353ef7458b0e01"}, "results": {"Sheaf.Paper.AdicOperationDomainsSourceComparison": {"hash": "2e48216f8679052116f7646d12477accfd1c91d4", "status": "OK"}, "Sheaf.Paper.AllStageCtfPullbackUnit": {"hash": "f05e3fb858d60f6d7b8308eeea68ff0f6aadc31a", "status": "SLOW"}, "Sheaf.Paper.CommonConstantUnitFrobenius": {"hash": "35e0636842df571094c943c61fea9cbff1703952", "status": "OK"}, "Sheaf.Paper.PointWeilPairingCoordinates": {"hash": "bfa154bdcbd23685edbb6c734c2db5dbd1617508", "status": "OK"}, "Sheaf.Paper.PointWeilPairingRealization": {"hash": "2e869adba9a1186bcb44abe64fa91095dd13072b", "status": "OK"}}, "seconds": 133, "time": "2026-10-28T07:14:18+0800", "transitive": 0, "version": 1}
```

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
