# AlgebraicGeometry.ProEtale.DerivedNakayama.pullback_regular

## Reason

Restore `Sheaf.Paper.DerivedNakayamaResolution`, listed in `coord/rework.tsv` after the
cluster-restore rollback of 2026-10-20T10:47:43Z. Its live path is absent and its source
survives at `quarantine/Sheaf/Paper/DerivedNakayamaResolution.lean`. Restore that source
and close its regular-module pullback equality. The transported action and the action
of the transported regular ring object are definitionally identical.

## Old

The live file is absent. In the archived module the affected declaration is:

```lean
theorem pullback_regular (X : Scheme.{u}) :
    (pullback l E X).obj (Mod.regular (integerRing l E)) =
      Mod.regular (condensedRingObj (integerRing l E) X) := by
  sorry
```

## New

Restore the entire archived file, changing only the above proof body:

```lean
theorem pullback_regular (X : Scheme.{u}) :
    (pullback l E X).obj (Mod.regular (integerRing l E)) =
      Mod.regular (condensedRingObj (integerRing l E) X) := by
  rfl
```

All declarations, signatures, definitions, attributes, imports and documentation otherwise
match the archive. The coefficient-definition attachment `def-sfb-torsion-stratum-coefficients`
and the theorem attachment `det-pe-derived-nakayama-resolution` are retained, together with
their dependencies. The main resolution theorem remains an open theorem with its original
statement and proof plan. No target's mathematical meaning changes.

## Users

There are no live direct importers in the local source snapshot; the missing-module state
also means the downstream tool needs `--allow-missing`. A search of `lean/` and `quarantine/`
finds these nine quarantined direct consumers. Each uses the restored identical public
interface. No consumer adaptation is required and no other quarantined module is restored.
The existing `regularPullbackIso` definition now uses the complete equality proof and has
underlying identity; the separate consumer check verifies that identity definitionally.

| module | group holding it | effect |
|---|---|---|
| Sheaf.SixFunctors.ProEtale.DerivedCompletion | no local claim record | Identical restored interface; no adaptation. |
| Sheaf.SixFunctors.ProEtale.IntegralOpenDirectImage | no local claim record | Identical restored interface; no adaptation. |
| Sheaf.Paper.DerivedNakayamaFirstReduction | no local claim record | Identical restored interface; no adaptation. |
| Sheaf.Paper.ProperHeartBoundTorsion | no local claim record | Identical restored interface; no adaptation. |
| Sheaf.Paper.IntegralCriterionReductions | no local claim record | Identical restored interface; no adaptation. |
| Sheaf.Paper.UniformConstructibleExtTorsion | no local claim record | Identical restored interface; no adaptation. |
| Sheaf.Paper.IntegralProperBaseChange | no local claim record | Identical restored interface; no adaptation. |
| Sheaf.Paper.DerivedNakayama | no local claim record | Identical restored interface; no adaptation. |
| Sheaf.Paper.IntegralDerivedCoefficientData | no local claim record | Identical restored interface; no adaptation. |

## Status

landed 20261021T022428-L-2846100 2026-10-21 (merge of deliver/B4/Sheaf.Paper.DerivedNakayamaResolution)
