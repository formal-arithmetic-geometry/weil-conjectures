# SmoothPurityCoefficientTowers proof elaboration options

## Reason

The completed proof needs Lean's backward definitional-equality elaborator to unfold
semireducible coefficient and limit constructions. Two local set_option commands enable
that elaboration. The stage-3 static checker conservatively treats changed commands as
an interface change and requests this record. They are local elaborator settings;
importers do not inherit them. No existing definition, signature, visibility, notation
or instance is changed, and no target meaning is changed.

## Old

```lean
set_option autoImplicit false
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## Users

Every direct importer listed below, and hence its importers, sees the same existing
public declarations with identical types and definition bodies. No adaptations are
needed. Group ownership is immaterial because these files are untouched.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SmoothPurityCoefficientTowers | Y6 | Proof elaboration only |
| Sheaf.Paper.CompactSupportUniformTorBound | unchanged; not adapted | None; options are local |
| Sheaf.Paper.IntegralDirectImageTower | unchanged; not adapted | None; options are local |
| Sheaf.Paper.SmoothPurityCoefficientTowersAbelian | unchanged; not adapted | None; options are local |
| Sheaf.Paper.SmoothPurityNormalizedEquivalence | unchanged; not adapted | None; options are local |
| Sheaf.Paper.SmoothPurityReductionTowerNormalized | unchanged; not adapted | None; options are local |
| Sheaf.Paper.SmoothPurityTowerBound | unchanged; not adapted | None; options are local |
| Sheaf.Paper.SmoothPurityTowerInjectiveComponents | unchanged; not adapted | None; options are local |
| Sheaf.Paper.SmoothPurityTowerLevels | unchanged; not adapted | None; options are local |
| Sheaf.Paper.SmoothPurityTowerReconstruction | unchanged; not adapted | None; options are local |

## Status

landed 20261019T034359-L-427228 2026-10-19 (merge of deliver/Y6/Sheaf.Paper.SmoothPurityCoefficientTowers)
