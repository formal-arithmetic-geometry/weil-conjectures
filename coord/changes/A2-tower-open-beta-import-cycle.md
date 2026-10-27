# Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization imports

## Reason

The calculus proof needs ProperOpenAlphaPasting and TowerMateEvaluationScalars, as its
DAG specifies. Both depend on StrictTowerOrdinaryProperOpenArrows, which depends on
TowerOpenBetaNormalization. The latter unnecessarily imports the calculus, closing an
import cycle when the planned proof dependencies are used. Remove that single import.
No declaration of TowerOpenBetaNormalization uses a declaration introduced by the calculus.
The beta node has no calculus statement or proof dependency.

## Old

```lean
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
```

## New

The line above is removed. Every declaration, signature, proof, attribute and other
import in TowerOpenBetaNormalization is preserved verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization | Y3 | Only the unused import is removed, to break the cycle. |
| Sheaf.AlgebraicGeometry.StrictTowerOrdinaryProperOpenArrows | S9 | No calculus declarations used; unchanged source compiles. |
| Sheaf.AlgebraicGeometry.ProperOpenAlphaPasting | V2 | No calculus declarations used; unchanged source compiles. |
| Sheaf.AlgebraicGeometry.TowerMateEvaluationScalars | X2 | No calculus declarations used; unchanged source compiles. |
| Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus | A2 | May now use its planned proof dependencies. Public signatures and definitions remain unchanged. |

The three downstream modules above are the complete output of
`tools/downstream.py Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization` at the shared
source snapshot. Searching them for all public calculus declaration names finds no uses.
Byte-identical sandbox copies of the three consumers only rebuild their artifacts against
the changed import graph; they introduce no delivery diff.

## Status

landed 20261023T230259-L-3403299 2026-10-23 (merge of deliver/A2/Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus)
