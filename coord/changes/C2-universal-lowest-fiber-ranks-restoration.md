# AlgebraicGeometry.Scheme.universalLowest_fiber_ranks

## Reason

Restore the zero-hole module preserved at the quarantine path in
`coord/rework.tsv`. Its complete proof needs the current adopted composition API
and an explicit evaluation universe/additive instance. This changes no statement,
definition or public import, and reopens no target statement review.

## Old

The archived proof imports:

```lean
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
```

Its zero-object transport uses:

```lean
    have hzv : IsZero (derivedFiberCohomology S E i (h t)) :=
      (ModuleCat.restrictScalars (ΓSpecIso (S.residueField (h t))).inv.hom).map_isZero
        ((SheafOfModules.evaluation
          (moduleRings (Spec (S.residueField (h t))).toRingedSpace)
          (Opposite.op ⊤)).map_isZero hz')
```

## New

```lean
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
```

```lean
    have : (SheafOfModules.evaluation.{u}
        (moduleRings (Spec (S.residueField (h t))).toRingedSpace)
        (Opposite.op ⊤)).Additive :=
      inferInstanceAs ((SheafOfModules.forget _ ⋙
        PresheafOfModules.evaluation _ (Opposite.op ⊤)).Additive)
    have hzv : IsZero (derivedFiberCohomology S E i (h t)) :=
      (ModuleCat.restrictScalars (ΓSpecIso (S.residueField (h t))).inv.hom).map_isZero
        ((SheafOfModules.evaluation.{u}
          (moduleRings (Spec (S.residueField (h t))).toRingedSpace)
          (Opposite.op ⊤)).map_isZero hz')
```

The signatures of the public theorem and both private helper theorems are verbatim
unchanged. All four public imports remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks | C2 | Restored; proof compiles with zero holes. |
| Sheaf.AlgebraicGeometry.PerfectUniversalLowestZeroModel | unclaimed in local claim records | Same theorem signature and public imports; no adaptation required. |

The item is absent from the downstream index while quarantined. Direct searches
of both Lean roots, quarantine and DAG nodes found the above consumer and its
matching parent node `lem-sc-perfect-universal-lowest-zero-model`. No other module
is adapted in this packet.

## Status

landed 20261020T211640-L-3482824 2026-10-20 (merge of deliver/C2/Sheaf.AlgebraicGeometry.UniversalLowestFiberRanks)
