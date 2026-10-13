# strictHenselizationRing_noetherian_of_regular imports

## Reason
The proof uses the regular-divisor quotient theorem and obtains nontriviality from strictHenselizationLocalStructure. StrictHenselizationLocalStructure becomes a private proof import; StrictHenselizationNoetherian is removed. The changed public imports are recorded for review.

## Old
```lean
public import Sheaf.Paper.StrictHenselizationLocalStructure
public import Sheaf.RingTheory.StrictHenselizationNoetherian
```

## New
```lean
import Sheaf.Paper.StrictHenselizationLocalStructure
-- Sheaf.RingTheory.StrictHenselizationNoetherian removed
```

## Users
| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian | V3 | compiles with the pruned import list |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient | unclaimed | original source compiles against the changed imports; signature unchanged |

## Status
landed 20261013T161322-L-1424596 2026-10-13 (merge of deliver/V3/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotientNoetherian)
