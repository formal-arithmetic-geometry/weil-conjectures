# Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence interface

## Reason

The proof imports two helper modules and uses backward definitional equality
transparency options for its componentwise categorical calculations. The static
interface checker flags the added file-level commands, so this record documents
them and the associated proof-import changes. Options govern elaboration of this
file; plain proof imports do not export the helper statements to importers.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProperOpenCalculus
import Sheaf.AlgebraicGeometry.CompactifiableCompatibleTower
import WeilConjectures.Compactification.CategoryBaseChange

@[expose] public section
set_option autoImplicit false
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProperOpenCalculus
import Sheaf.AlgebraicGeometry.ProperOpenTowerRefinement
import Sheaf.AlgebraicGeometry.ProperOpenStaircase

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

The two new helper imports are proof imports and add only the proved helper
declarations recorded by their new nodes. The old geometric imports are unused by
the proof and were removed. The transparency options are required for elaboration of
the explicit categorical pasting calculations and do not alter any theorem signature.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoefficientTowerShriekCalculus | unclaimed | imports the coherence module; its declarations and signatures are unchanged |
| Sheaf.Paper.CompactSupportLerayFiltration | unclaimed | downstream import; unchanged |
| Sheaf.Paper.FieldShriekCompositionQcqs | unclaimed | imports the coherence module; unchanged |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | downstream import; unchanged |
| Sheaf.Paper.VerdierExchange | unclaimed | downstream import; unchanged |
| Sheaf.Paper.ZlFrobeniusCompactSupportComparison | unclaimed | downstream import; unchanged |
| Sheaf.Paper.ZlShriekComposition | unclaimed | downstream import; unchanged |

## Status

landed 20261019T005405-L-2762862 2026-10-19 (merge of deliver/Q5/Sheaf.AlgebraicGeometry.CompactificationRefinementCoherence)
