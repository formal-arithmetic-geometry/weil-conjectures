# AlgebraicGeometry.Scheme.Modules.scalarCup_pullback_naturality

## Reason

Restore the module assigned by coord/rework.tsv from its quarantine archive.
The archive publicly imports the withdrawn empty scalar operations module. Its
unmodified source fails at line 54 with `Unknown identifier Field`, imported
privately. The definitions used by the public theorem now belong to the adopted
upstream operations module. Import that canonical module publicly instead.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
```

The theorem signature, docstring, complete proof, and three proof-only imports
are identical to the quarantine archive. No source-library declaration,
definition, instance, target statement, or mathematical dependency changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality | B5 | Restored; public statement can access its canonical scalar operations. |
| Sheaf.AlgebraicGeometry.ScalarCupPullbackCoefficientNaturality | quarantined, no local claim | Sole archived direct importer and theorem user; theorem signature unchanged. Its own stale public import needs an independent restoration repair. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcohFunctoriality | quarantined | Transitive consumer through ScalarCupPullbackCoefficientNaturality; unchanged theorem meaning and interface. |
| Sheaf.AlgebraicGeometry.PicardKunnethQcoh | quarantined | Transitive consumer through PicardKunnethQcohFunctoriality; unchanged theorem meaning and interface. |

Searched both lean/ and quarantine/ for the module and theorem. There are no
live Lean importers. tools/downstream.py reports `unknown module(s)` because the
item is absent from lean/, so its archived direct consumer was checked explicitly.
A validation-only consumer copy reproduced its own line-51 `Unknown identifier
Field` error; replacing only its stale public import by the canonical operations
module made its unchanged proof compile without warnings in 6.2 seconds against
the restored item. This validation copy is not delivered.
The DAG parent lem-sc-scalar-cup-pullback-coefficient-naturality still uses the
restored theorem. No downstream adaptation is forced by replacing the empty
import with the canonical definitions. The operation node already points to that
upstream module, and the item's Lean attachment and all three proof steps still
match its restored theorem. No target definition changes or semantic target
review is needed.

## Status

landed 20261020T233054-L-890329 2026-10-20 (merge of deliver/B5/Sheaf.AlgebraicGeometry.ScalarCupPullbackNaturality)
