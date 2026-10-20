# AlgebraicGeometry.isIso_residue_stalk_homologyMap

## Reason

Restore the quarantined comparison module after upstream sync 5f7b33eac.
Its rework row records an environment collision: both the old Sheaf import and
WeilConjectures.AlgebraicGeometry.DerivedPullback supplied
AlgebraicGeometry.derivedPullback. The canonical definition node now attaches to
the WeilConjectures module; the old Sheaf module has been withdrawn.
Use that canonical module directly, preserving the existing comparison argument.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

No declaration signature, definition body or theorem proof is edited. The theorem
now refers to the adopted derived pullback already used by both comparison
lemmas. Its binders, homology assertion and local instance expressions are the
archived ones. The canonical definition migration was reviewed separately under
def-pc-derived-pullback; this packet restores a consumer of that interface.

## Users

The source-only downstream script reports an unknown module because the item is
quarantined. A search of lean/ and quarantine/ finds the direct importer and
consumer below. The other two rows are quarantined DAG parents named by rework;
their dependence remains and is not pruned. No consumer needs an adaptation:
the public theorem has the same name and textual signature.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ResidueStalkHomologyMapComparison | P4 | Restore with canonical public import; compiles in 12.2 seconds. |
| Sheaf.AlgebraicGeometry.ResidueHomologyRankOneCoefficient | Not determined; not edited | Quarantined direct importer and caller at line 172; same theorem interface. |
| Sheaf.AlgebraicGeometry.RankOneResidueStalkComponent | Not determined; not edited | Quarantined parent; no statement or dependency change. |
| Sheaf.AlgebraicGeometry.ConnectiveRankOneModelStalk | Not determined; not edited | Quarantined parent; no statement or dependency change. |

## Status

landed 20261020T174832-L-805953 2026-10-20 (merge of deliver/P4/Sheaf.AlgebraicGeometry.ResidueStalkHomologyMapComparison)
