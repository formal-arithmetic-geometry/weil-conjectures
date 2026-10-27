# AlgebraicGeometry.Scheme.rootTower_finite_tensor

## Reason

Preflight classifies the added proof-elaboration commands as a change to what importers
see. The proof marks `SheafOfModules.scalarExtensionLift` locally irreducible to avoid
unfolding the large scalar-extension adjunction while comparing morphisms. The additional
transparency option permits definitional comparison of the existing module interfaces.
Both commands are confined to this module. No existing declaration signature, visibility,
public import, attribute on a public declaration, or non-theorem definition is changed.
There is no mathematical interface change and no forced adaptation.

## Old

The module did not contain either of these commands:

```lean
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.scalarExtensionLift
```

All existing public definitions and the statement of `rootTower_finite_tensor` remain
verbatim. Its former proof was `by sorry`.

## New

```lean
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] SheafOfModules.scalarExtensionLift
```

The theorem now has a complete proof, using only proved private helpers. The local
attribute affects elaboration of the remaining proofs in this file. It does not alter
the definition of `scalarExtensionLift` or its behavior for importers.

## Users

`python3 tools/downstream.py Sheaf.Paper.RootTowerFiniteTensor --uses
rootTower_finite_tensor` reports zero downstream modules and one textual use, in the
item itself. Unfinished DAG parents remain attached; no withdrawal is proposed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.RootTowerFiniteTensor | C3 | Complete theorem proof; private elaboration controls. |

No source-library module is changed. No target definition changes meaning, and no target
statement needs a renewed semantic review.

## Status

landed 20261023T151808-L-409983 2026-10-23 (merge of deliver/C3/Sheaf.Paper.RootTowerFiniteTensor)
