# WeilConjectures.PrincipalIntrinsicCompletion.tower and fiber

## Reason

Explicit return types keep the principal tower and its fiber in the coefficient-module
presentation used by their arguments. Previously the inferred result types retained the
presentation obtained by forgetting the completed commutative-ring sheaf. These are
definitionally equal categories, but repeatedly comparing their abelian and product
structures makes the normalized unit proof exceed the single-file compilation limit.
The bodies are unchanged. These annotations select a stable presentation without changing
an object, map, hypothesis or conclusion. Target meanings are unchanged by definitional
equality; this interface repair is nevertheless submitted for independent review.

## Old

```lean
abbrev tower (P : CochainComplex (Modules l E W) ℤ) :=
  koszulTowerComplex (completedIntegralCommRingSheafUnrestricted l E W) (sourceTower l E W P)

def fiber (P : CochainComplex (Modules l E W) ℤ) :=
  CochainComplex.mappingCocone (-roosU (tower l E W P))
```

## New

```lean
abbrev tower (P : CochainComplex (Modules l E W) ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ Modules l E W) ℤ :=
  koszulTowerComplex (completedIntegralCommRingSheafUnrestricted l E W) (sourceTower l E W P)

def fiber (P : CochainComplex (Modules l E W) ℤ) :
    CochainComplex (Modules l E W) ℤ :=
  CochainComplex.mappingCocone (-roosU (tower l E W P))
```

## Users

The current repository has one downstream module, RoosIntrinsicUnitComparison. Searches
for the qualified names identify that same module. The tensor/scalar module newly added
by this delivery also imports PrincipalIntrinsicCompletion. The latter uses its tensor
unit API and does not change the principal tower or fiber. PrincipalIntrinsicCompletion
has no current group claim. No adopted source-library module is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PrincipalIntrinsicCompletion | unclaimed | Only the two explicit return annotations above; all bodies and other declarations unchanged. |
| Sheaf.Paper.RoosIntrinsicUnitComparison | H6 | Uses the same tower and fiber; corresponding quotient tower and comparison receive explicit result types in the accompanying change record. |
| Sheaf.Paper.QuotientTensorScalarTowerComparison | H6 (new) | Imports the unchanged tensor-unit API. |

## Status

landed 20261022T114205-L-583187 2026-10-22 (merge of deliver/H6/Sheaf.Paper.RoosIntrinsicUnitComparison)
