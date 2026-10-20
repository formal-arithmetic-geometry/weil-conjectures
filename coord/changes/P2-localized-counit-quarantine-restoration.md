# AlgebraicGeometry.derivedPullbackComposition_localized_counit

## Reason

Restore the assigned quarantined module from the archive recorded in
coord/rework.tsv. The upstream sync made derivedPullback globally irreducible.
Lean therefore rejects the archived redundant local irreducibility attribute.
Removing that name from the local attribute command repairs the recorded error.
The existing theorem and all three private proofs are retained verbatim.

## Old

The archived module has:

```lean
attribute [local irreducible] derivedPullback Scheme.Modules.tensorPullback
  DerivedCategory.Qh canonicalDerivedPullbackComposition
```

The module is absent from lean/ and retained at
quarantine/Sheaf/AlgebraicGeometry/DerivedPullbackCompositionLocalizedCounit.lean.

## New

The restored module has:

```lean
attribute [local irreducible] Scheme.Modules.tensorPullback
  DerivedCategory.Qh canonicalDerivedPullbackComposition
```

derivedPullback retains its upstream irreducibility. No declaration signature,
proof, definition body, public import, exported attribute or target meaning changes.
The restored module compiles through lcompile.py in 51.2 seconds with zero holes.
Its existing DAG attachment and proof dependencies remain valid without edits.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionLocalizedCounit | P2 | Restored with the redundant local attribute removed. |
| Sheaf.AlgebraicGeometry.DerivedPullbackCompositionCounitNormalization | unclaimed | Quarantined direct importer; theorem signature and public imports preserved. |

The current source tree has no other importers or references to this Sheaf module
or its declaration. The separate upstream module and its upstream consumer stay
unchanged. The retirement record explicitly keeps this copy because its upstream
twin reaches the upstream twins of other retained dependencies; this repair does
not attempt a retirement. The quarantine archive is preserved.

## Status

landed 20261020T145535-L-2409124 2026-10-20 (merge of deliver/P2/Sheaf.AlgebraicGeometry.DerivedPullbackCompositionLocalizedCounit)
