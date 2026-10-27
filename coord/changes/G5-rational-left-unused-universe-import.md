# Sheaf.Paper.RationalLeftCoefficientLocalization

## Reason

The item's statement and its completed proof use the published equal-universe
integral scalar extension, already imported through `SfScalarExtensionComposition`.
They never use either independent-universe wrapper or its additive instance.
Remove the unnecessary import as required by stage-3 pruning.

## Old

```lean
public import Sheaf.Paper.IntegralScalarExtensionUniverses
```

## New

The above import is removed. All public declaration signatures and all other
public imports of the item are unchanged. The universe-wrapper module itself
and its declarations are preserved.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.RationalLeftCoefficientLocalization | G5 | Unused import removed; theorem unchanged. |

`python3 tools/downstream.py Sheaf.Paper.RationalLeftCoefficientLocalization
--uses integralScalarExtensionOfUniverses integralScalarExtensionComparisonOfUniverses`
finds zero downstream modules and zero uses. The direct-import search
`rg -l '^(public )?import Sheaf.Paper.RationalLeftCoefficientLocalization$' lean/`
finds none. There are therefore no direct importers to adapt or compile.
The item remains available to its unfinished DAG parents; no node or module is withdrawn.

## Status

landed 20261026T091631-L-3360091 2026-10-26 (merge of deliver/G5/Sheaf.Paper.RationalLeftCoefficientLocalization)
