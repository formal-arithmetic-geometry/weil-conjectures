# CategoryTheory.ScalarLocalization

## Reason

The general R-linear tensor-Hom category uses no coefficient field, uniformizer theorem,
or p-adic declaration. Its sole direct consumer also uses none of those declarations.
Remove the unused public import of the coefficient-field localization theorem. This
prunes an independent unproved theorem and its supporting modules from this import path.
Every existing declaration signature, definition body and instance remains identical.
No target statement or meaning changes.

## Old

```lean
public import Sheaf.CategoryTheory.LinearScalarLocalization
public import Sheaf.NumberTheory.Padics.IntegersLocalizationUniformizer
```

## New

```lean
public import Sheaf.CategoryTheory.LinearScalarLocalization
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.ScalarLocalizationTriangulated | claimed; no adaptation | No p-adic names are used. Original consumer compiled against the pruned module; no adaptation. |

`tools/downstream.py Sheaf.CategoryTheory.ScalarLocalization --uses ScalarLocalization`
found exactly this one downstream module. The coefficient module's only direct importer
was ScalarLocalization. No declaration bodies or signatures change, so the mathematical
meaning of all users is unchanged.

## Status

landed 20261018T062907-L-674429 2026-10-18 (merge of deliver/S2/Sheaf.CategoryTheory.ScalarLocalization)
