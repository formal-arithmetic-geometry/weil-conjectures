# SheafOfModules.StrictScalarHom.exists_scalarHomChainEvaluation

## Reason

The complete proof introduces proved private helpers. Four helper theorems use
`omit ... in` to avoid unused-section-variable warnings. The preflight command scanner
classifies these local commands as a change to what importers see. Each command applies
only to the immediately following private theorem. No exported declaration, instance,
attribute, notation, option, or public import changes.

## Old

The item had no `omit` commands and no private proof helpers. Its theorem had the existing
unchanged signature and proof `:= by sorry`.

## New

The public theorem has exactly its original signature and a complete proof. Its only new
import is private:

```lean
import Sheaf.Algebra.Homology.SliceScalarHomChainAdjunction
```

The following local command precedes each of the private theorems `homMap_comp`,
`evaluate_map`, `evaluate_ext`, and `evaluate_smul`:

```lean
omit [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  [HasWeakSheafify J AddCommGrpCat.{max c v u}] in
```

These omit unused assumptions only from private helpers, all proved without sorry.
No consumer adaptation is required. The target statements and all definitions they
use retain their meanings.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.ScalarHomChainEvaluation | C4 | Original hole closed; public signature unchanged. |
| Sheaf.Algebra.Homology.ScalarHomChainCoefficientCoherence | unclaimed | Imports the item; exported interface unchanged, so no adaptation. |

`tools/downstream.py ... --uses SheafOfModules.StrictScalarHom.exists_scalarHomChainEvaluation`
reports the item itself as the sole textual declaration-name occurrence and reports the
coefficient coherence module as the sole downstream module. The latter currently imports
the item for its unfinished proof.

## Status

landed 20261021T120331-L-3789908 2026-10-21 (merge of deliver/C4/Sheaf.Algebra.Homology.ScalarHomChainEvaluation)
