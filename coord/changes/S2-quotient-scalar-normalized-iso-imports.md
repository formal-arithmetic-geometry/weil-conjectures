# AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalar_section_ordinary_normalized_isIso

## Reason

The normalized-map existence theorem is not used to prove invertibility of a map that
is already supplied as an argument. Import the statement data directly and use the
existing internal/section scalar-adjunction comparison privately in the proof.
The theorem statement, attributes and visibility stay identical.

## Old

```lean
public import Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedMap
```

## New

```lean
public import Sheaf.Paper.QuotientSectionTensorData
import Sheaf.CategoryTheory.InternalSectionScalarAdjunction
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
```

## Users

`tools/downstream.py ... --direct --uses scalar_section_ordinary_normalized_isIso`
finds one direct importer; repository search finds no other use of the declaration.
The dependency closure has many indirect importers, but no existing declaration is
renamed or changed. The sole direct importer independently imports the normalized-map
module, so its access to that theorem is preserved.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedIso | S2 | proof completed; unused public import replaced by its data dependency |
| Sheaf.Paper.QuotientScalarSectionOrdinaryComparisonExistence | unclaimed | unchanged; separately imports the normalized-map module; compile checked against this delivery |

## Status

landed 20261027T234303-L-88630 2026-10-27 (merge of deliver/S2/Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedIso)
