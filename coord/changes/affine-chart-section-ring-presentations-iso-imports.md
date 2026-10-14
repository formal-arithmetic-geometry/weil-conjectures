# AlgebraicGeometry.affine_chart_section_ring_presentations_iso

## Reason

The proved theorem needs only Mathlib. Its old public imports brought in
unrelated project base-change and limiting-cone theory. Prune those imports
and supply the statement's Mathlib dependencies directly. No declaration's
signature or visibility changes, and no definition changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.AffineChartUpperTailLimitData
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Order.Antisymmetrization
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Antisymmetrization
```

## Users

`tools/downstream.py` reports 1414 transitive importers. With `--uses
affine_chart_section_ring_presentations_iso`, only the following two modules
mention the declaration. With `--direct`, the sole importer is
`Sheaf.AlgebraicGeometry.AffineChartSectionRingPresentations`.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineChartSectionRingPresentationsIso | U2 | The theorem is proved from Mathlib; pruned public import surface. |
| Sheaf.AlgebraicGeometry.AffineChartSectionRingPresentations | unclaimed in this checkout | No adaptation: already publicly imports all three removed modules independently, and imports Iso privately. |

Every transitive importer therefore retains the original dependency imports
through AffineChartSectionRingPresentations. Its public imports provide all
previously exported objects, and its use of the theorem has unchanged type.
No forced adaptation is necessary. No target definition or statement changes.

## Status

landed 20261014T013048-L-3418519 2026-10-14 (merge of deliver/U2/Sheaf.AlgebraicGeometry.AffineChartSectionRingPresentationsIso)
