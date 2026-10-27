# Sheaf.Paper.EtaleTorFlatPullbackModel public imports

## Reason

The shorter proof uses ordinary ModuleCat-valued inverse image, whose additivity and
exactness already come from Derived.UpperLowerStar. The general ringed-module
inverse-image comparison is unnecessary. Remove its public import. All declaration
signatures, visibility, the existing isomorphism definition and its body are unchanged.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
```

## New

This import is removed; no replacement public import is added. The proof-only import
of Sheaf.AlgebraicGeometry.EtaleConstantModuleFlat supplies the flatness equivalence
and the existing instance for preservation of flat modules by geometric inverse image.

## Users

`tools/downstream.py Sheaf.Paper.EtaleTorFlatPullbackModel --uses
etale_tor_flat_pullback_model etaleTorFlatPullbackModelIso` reports zero downstream
modules. Only the item itself refers to these declarations. No consumer needs adapting.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleTorFlatPullbackModel | R1 | Remove unused public import; all statements and definitions unchanged. |

## Status

landed 20261024T204650-L-3817320 2026-10-24 (merge of deliver/R1/Sheaf.Paper.EtaleTorFlatPullbackModel)
