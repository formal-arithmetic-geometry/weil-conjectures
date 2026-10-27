# GeneralPairHomCoordinates public imports

## Reason

The normalized Hom theorem needs the existing intrinsic pair and colimit
constructions, already exported by GeneralAlgebraicallyClosedCoefficients.
It neither states nor uses the ExactStagePairData structure. Remove that
redundant import after proving the ten-clause theorem.

## Old

```lean
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
public import Sheaf.CategoryTheory.ExactStagePairData
```

## New

```lean
public import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.GeneralPairHomCoordinates | F2 | Existing statement unchanged; proof uses the retained public coefficient API. |

There are no current Lean direct importers of the assigned module, as checked
with `rg` over lean/. No downstream file requires adaptation. The dependency
node for the common-stage pair construction remains used through the existing
quotient representatives and is not withdrawn.

## Status

landed 20261027T094401-L-220592 2026-10-27 (merge of deliver/F2/Sheaf.Paper.GeneralPairHomCoordinates)
