# constantSubsheaf_finite_filtration imports

## Reason

The theorem statement needs the extension-by-zero definitions. The induction does not use the extension-by-zero stalk results. Remove their unused direct import and expose the extension-by-zero definitions directly.

## Old

```lean
public import Sheaf.Topology.AbelianOpenExtensionByZeroStalks
```

## New

```lean
public import Sheaf.Topology.AbelianOpenExtensionByZero
```

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.Topology.NoetherianExtensionByZeroReduction` | none; no adaptation | Its existing public import of `Sheaf.Topology.AbelianOpenExtensionByZeroStalks` supplies the same stalk declarations directly. No statement, definition or proof changes. |

Source import search found this sole direct importer. No declaration signature or definition changes, including any target. No module adaptation is required.

## Status

landed 20261012T053944-L-2640999 2026-10-12 (merge of deliver/N1/Sheaf.Topology.ConstantSubsheafFiniteFiltration)
