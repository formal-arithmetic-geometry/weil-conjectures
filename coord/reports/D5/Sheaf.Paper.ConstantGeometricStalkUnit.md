## What changed

Reduced `WeilConjectures.ConstantGeometricStalkUnit.finiteOperator_unit` to the
composition law for the canonical finite coefficient multiplication and the
one-step point transport calculation on the regular coefficient object. The
module now proves equality of every iterated finite Weil map with its canonical
unit map, transport normalization for every map to the regular unit, and the
return-square cancellation. All existing public signatures and definitions are
preserved. New imports are private proof imports.

Added `Sheaf.Paper.FinitePullbackUnitComposition` and
`Sheaf.Paper.FinitePointTransportUnit`, each with one public, strictly smaller
statement and its DAG node. Updated the item's finite proof steps to follow the
Lean induction. The integral and rational proof plans are retained.

Validation: the two new modules compiled in 5.0 and 4.2 seconds, and the
updated item compiled in 41.1 seconds through `lcompile.py`.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.ConstantGeometricStalkUnit.finiteOperator_unit` by decomposition,
not by a complete proof independent of new holes. Two new holes are added:

- `WeilConjectures.ConstantGeometricStalkUnit.finiteUnit_composition`
  (`lem-zl-finite-pullback-unit-composition`).
- `WeilConjectures.ConstantGeometricStalkUnit.finitePointTransport_unit`
  (`lem-zl-finite-point-transport-unit`).

The following original holes remain unchanged in the item:

- `WeilConjectures.ConstantGeometricStalkUnit.integralOperator_unit`.
- `WeilConjectures.ConstantGeometricStalkUnit.rationalOperator_scalar`.

Both belong to `lem-zl-constant-geometric-stalk-unit`. Thus one of the three
original holes is reduced to two lower holes: two holes remain in the item and
four holes remain in the delivery as a whole. There are no holes in definitions
or private helpers. Existing proved declarations, including the rational
operator deduction, remain proved.

## No longer needed

None. No public import, module, node, or unit step is withdrawn. The integral and
rational clauses still need their original proof dependencies. The finite proof
now uses the two named lower statements and existing transport naturality.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed. The original DAG called the finite
compositor and one-step transport calculations elementary, but the module had
no declarations expressing these normalized equations. They are now separate
items; the induction and return-square pasting are actual Lean proofs. Searches
found ordinary pullback unit and compositor lemmas, but no exact theorem for
these specified coefficient-coordinate maps.

The current blueprint places `prop-every-iterate-trace.proof.md` under
`sk-thm-intfactors`; the new references use `literature/blueprint/latest` and that
current path. The existing declaration docstrings are preserved.

## New nodes

`lem-zl-finite-pullback-unit-composition` states the canonical finite compositor's
compatibility with regular multiplication for any composable scheme maps. It is
step 3 of the original expansion and contains neither Frobenius iteration nor a
local operator. Its Lean module is `Sheaf.Paper.FinitePullbackUnitComposition`.

`lem-zl-finite-point-transport-unit` states only the one-step identity at the
coefficient point. It is the generator calculation of step 4, without a returning
geometric point, a return square, or an iterated Weil map. Its Lean module is
`Sheaf.Paper.FinitePointTransportUnit`.

## Related modules compiled before delivery

7 related module(s) compiled against this delivery by deliver3.py: 7 INFRA.

```json
{"capped": false, "direct": 7, "left_out": 0, "own": {"Sheaf.Paper.ConstantGeometricStalkUnit": "38b1c2c13e6efa4d73a60a1db6785286a6687ee3", "Sheaf.Paper.FinitePointTransportUnit": "5459f07bb6d835687c5b5de1241c8b3e13693c4d", "Sheaf.Paper.FinitePullbackUnitComposition": "f587ba10c6660f39bc917febfe303f7adcbab339"}, "results": {"Sheaf.Paper.AdicOperationDomainsSourceComparison": {"hash": "2e48216f8679052116f7646d12477accfd1c91d4", "status": "INFRA"}, "Sheaf.Paper.AllStageCtfPullbackUnit": {"hash": "f05e3fb858d60f6d7b8308eeea68ff0f6aadc31a", "status": "INFRA"}, "Sheaf.Paper.CommonConstantUnitFrobenius": {"hash": "3e24bc10013089f3622934ae5565cdfaabe43f79", "status": "INFRA"}, "Sheaf.Paper.IntegralConstantUnitFrobenius": {"hash": "cc89211672d1ac6acd92c5f919d71bc3e1d73096", "status": "INFRA"}, "Sheaf.Paper.PointWeilPairingCoordinates": {"hash": "bfa154bdcbd23685edbb6c734c2db5dbd1617508", "status": "INFRA"}, "Sheaf.Paper.PointWeilPairingRealization": {"hash": "2e869adba9a1186bcb44abe64fa91095dd13072b", "status": "INFRA"}, "Sheaf.Paper.RationalConstantUnitFrobenius": {"hash": "b08713168d8755e069980d389888c79debfcc4d3", "status": "INFRA"}}, "seconds": 149, "time": "2026-10-28T10:27:45+0800", "transitive": 0, "version": 1}
```

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
