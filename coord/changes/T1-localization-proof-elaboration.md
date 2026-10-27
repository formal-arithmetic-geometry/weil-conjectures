# SfQbarLocalizationCommonStage proof elaboration commands

## Reason

The assembly proof keeps the large intrinsic-category and finite triangulation
constructions locally irreducible. The backward unifier respects those boundaries.
The static interface checker conservatively flags changed commands. These local
attributes and options do not propagate to importers. Every existing public
signature, definition body, visibility and public import is preserved. The change
has no effect on the meaning of a target.

## Old

```lean
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

## New

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] sfIntegralConstructible FrobeniusExchange.models
  sfRationalTriangulationDatum
```

The existing definition `sfQbarLocalizationSourceIso` is elaborated under its own
`set_option backward.isDefEq.respectTransparency false in`; its body is unchanged.
A single proof-local
`set_option linter.flexible false in` permits the documented dependent identity
simplification in `localizationAdjunctionShift`. These alter proof checking only.

## Users

`tools/downstream.py Sheaf.Paper.SfQbarLocalizationCommonStage --uses
sfQbarLocalizationCommonStage` lists the following downstream modules. None needs
an adaptation; the existing public declarations have identical types and bodies.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SfQbarLocalizationCommonStage | T1 | Proof elaboration only |
| Sheaf.Paper.AdicProperAdjunctionRealization | unchanged; not adapted | None; commands are local |
| Sheaf.Paper.AdicQbarConstructibleRealization | unchanged; not adapted | None; commands are local |
| Sheaf.Paper.AdicRealizationIsomorphismNormalization | unchanged; not adapted | None; commands are local |
| Sheaf.Paper.NativeProperCoefficientOperations | unchanged; not adapted | None; commands are local |
| Sheaf.Paper.NativeProperTensorComparison | unchanged; not adapted | None; commands are local |
| Sheaf.Paper.NativeWeilScalarCounitCategories | unchanged; not adapted | None; commands are local |
| Sheaf.Paper.NativeWeilScalarCounitData | unchanged; not adapted | None; commands are local |
| Sheaf.Paper.NativeWeilScalarFrobeniusCounit | unchanged; not adapted | None; commands are local |
| Sheaf.WeilSheaf.NativeExceptionalForgetful | unchanged; not adapted | None; commands are local |

## Status

landed 20261025T101416-L-3690709 2026-10-25 (merge of deliver/T1/Sheaf.Paper.SfQbarLocalizationCommonStage)
