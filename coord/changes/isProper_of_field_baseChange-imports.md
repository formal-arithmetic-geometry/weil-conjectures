# AlgebraicGeometry.isProper_of_field_baseChange (public import pruning)

## Reason

The theorem's signature uses only Mathlib's morphism and pullback definitions.
`BaseChangeConventions` contributes no statement or proof used by this module.
Remove its public import to prune the unused dependency. No declaration signature,
definition or target statement changes.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.BaseChangeConventions
import Sheaf.AlgebraicGeometry.FieldExtensionFpqcCover
import Sheaf.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import Sheaf.AlgebraicGeometry.UniversallyClosedOfFpqcCover
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.AlgebraicGeometry.FieldExtensionFpqcCover
import Sheaf.AlgebraicGeometry.IsSeparatedOfFlatSurjectiveBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.IsProperOfFieldBaseChange
--uses isProper_of_field_baseChange --direct` lists the following direct importer.
Its source uses the unchanged theorem at line 349 and mentions none of the
public declarations introduced by `BaseChangeConventions`; no adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IsProperOfFieldBaseChange | D3 | Proved unchanged theorem; unused public import removed. |
| WeilConjectures.AlgebraicGeometry.EffectiveDescent | Not changed by this delivery | Uses unchanged theorem; no base-change-conventions declarations used. |

## Status

landed 20261012T095856-L-314326 2026-10-12 (merge of deliver/D3/Sheaf.AlgebraicGeometry.IsProperOfFieldBaseChange)
