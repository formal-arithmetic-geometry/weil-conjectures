# module_extensionByZero_hom_formula

## Reason

The component Hom formula uses the explicit direct-sum construction and
sheafification, and does not use stalks. Remove the unused public stalk import
and the proof-only project stalk import. Private helpers use a local
`open SheafOfModules` command; no existing public declaration is changed.

## Old

```lean
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Sheaf.Topology.PresheafModuleStalkFunctor
```

## New

```lean
public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
```

The theorem's entire signature and visibility are identical. Added only fully
proved private helpers and `open SheafOfModules` inside its namespace.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroHomFormula | T2 | Sole original hole proved; unused imports removed. |
| Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction | unclaimed in local claims snapshot | Sole direct importer and sole external user of the theorem; independently imports both removed modules already. Signature and proof unchanged; no adaptation needed. |

`tools/downstream.py --uses module_extensionByZero_hom_formula` lists these two
users. There are 718 transitively downstream modules, but all paths through this
module pass through its sole direct importer, which explicitly imports the stalk
modules itself. Thus their imports and statements retain the same stalk interface.
No target statement or definition changes; no statement review is reopened.
A scratchpad check compiles the unchanged direct importer against the delivered
module. No adaptation of an existing module is included in this delivery.

## Status

landed 20261012T202253-L-708930 2026-10-12 (merge of deliver/T2/Sheaf.AlgebraicGeometry.Modules.ExtensionByZeroHomFormula)
