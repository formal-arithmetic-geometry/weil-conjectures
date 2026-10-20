# CategoryTheory.FiniteFilteredDerived.Presentation

## Reason

Restore the quarantined presentation without the unused filtered-complex-subquotient
public import. The archive's recorded failure was a duplicate filtration declaration
on the mixed old-Sheaf/upstream import paths. The current finite-filtration interface
uses the canonical upstream implementation; the presentation needs that interface,
not the cycle/boundary and complex-subquotient definitions. No declaration is changed.

## Old

```lean
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Predicate
```

## New

```lean
public import Sheaf.CategoryTheory.FiniteFiltrationInduction
public import Mathlib.Algebra.Homology.DerivedCategory.Plus
public import Mathlib.CategoryTheory.Localization.Predicate
```

All declaration signatures and definition bodies are verbatim unchanged. No target's
meaning changes, and no target statement review is reopened.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.CategoryTheory.FiniteFilteredDerivedPresentation` | R3 | Restore definitions, remove unused public import; compiled cleanly. |
| `Sheaf.CategoryTheory.FilteredFunctorGradedComparison` | unclaimed, quarantined | No change required: every public declaration compiles against the repaired interface in a probe omitting its unavailable independent proof import. |

`tools/downstream.py --allow-missing --uses Presentation` lists no live downstream
modules. Searching preserved quarantined sources finds the sole direct consumer above.
The consumer's original compile is blocked by its separate missing
`Sheaf.Algebra.Homology.FiniteFilteredLocalization` dependency. No consumer file is
included or modified in this delivery. The DAG node retains its Lean attachment
and dependencies; no upstream declaration or module is removed.

## Status

landed 20261020T162916-L-3674731 2026-10-20 (merge of deliver/R3/Sheaf.CategoryTheory.FiniteFilteredDerivedPresentation)
