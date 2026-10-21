# SheafOfModules.derivedScalarLocalizationReflection

## Reason

The direct exact-adjunction proof uses neither the general normalized derived coefficient
adjunction nor the cochain monoidal interface. Remove their explicit public imports from
`Sheaf.Algebra.Homology.DerivedScalarLocalizationReflection`. The theorem's signature and
all remaining public imports are unchanged. No definition used by a target changes.

## Old

```lean
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
```

## New

Both lines are removed. No declaration is replaced, removed or changed in type.
The proof imports `Mathlib.CategoryTheory.Localization.Adjunction` privately instead.
The remaining public imports provide every name in the unchanged theorem signature.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.DerivedScalarLocalizationReflection | H3 | Complete proof; remove two unused explicit public imports. |

`python3 tools/downstream.py Sheaf.Algebra.Homology.DerivedScalarLocalizationReflection
--uses derivedScalarLocalizationReflection` reports zero downstream modules and only
the declaration in its own module. Thus no consumer needs adaptation. The DAG parent
statements and the unit's route remain intact.

## Status

landed 20261021T134451-L-1168183 2026-10-21 (merge of deliver/H3/Sheaf.Algebra.Homology.DerivedScalarLocalizationReflection)
