# AlgebraicGeometry.isIso_residue_stalk_homologyMap

## Reason

Restore the quarantined comparison module after upstream sync 5f7b33eac. The rework
row records an environment collision: the old Sheaf copy and the adopted source copy
both declared `AlgebraicGeometry.derivedPullback`. The Sheaf copy is withdrawn, so the
restored module must import the canonical upstream declaration.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

The theorem signature, statement, proof and all declarations remain unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ResidueHomologyRankOneCoefficient | unclaimed/quarantined | Uses the theorem at line 172; its signature is unchanged. |
| Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent | unclaimed/quarantined | Downstream parent remains semantically unchanged. |
| Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk | repair reservation | Downstream parent remains semantically unchanged. |

## Status

landed 20261020T211637-L-3482190 2026-10-20 (merge of deliver/C1/Sheaf.AlgebraicGeometry.ResidueStalkHomologyMapComparison)
