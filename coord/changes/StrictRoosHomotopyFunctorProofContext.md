# CategoryTheory.roosF_homotopy_functor

## Reason

The complete proof needs private helpers with a shared category parameter and
elaboration settings for the existing cone and shift definitions. Preflight
conservatively treats the added `variable` and `set_option` commands as a change
to what importers see. This record documents those commands. The existing
public declarations, their signatures, all public imports, and docstrings stay
verbatim. The sole public theorem's proof hole is filled.

## Old

The relevant namespace-level proof context, after `namespace CategoryTheory`, is:

```lean
universe u v w
```

The current module's `set_option autoImplicit false` and
`open CategoryTheory.Limits Opposite` commands are preserved.

## New

The corresponding proof context is:

```lean
universe u v w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]
```

Every new declaration using the shared variable context is private. The existing
public theorem keeps its explicit category parameters and its signature verbatim.
These commands govern elaboration in this file; importers do not inherit the
variable context or these options. No global instance, notation, simp attribute,
or public helper is added. All new helper constructions and proofs compile.
The axiom probe accepts them with only the three permitted axioms.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.StrictRoosHomotopyFunctor | N2 | Private proof context and helpers; one hole closed. |
| Sheaf.CategoryTheory.InjectiveTowerRoosShifts | G9 | Imports the same public interface; no adaptation. |
| Sheaf.Paper.QuotientScalarComparisonDescent | unclaimed | Uses the theorem with the same signature; no adaptation. |
| Sheaf.Paper.ScalarPullbackStrictConeNaturality | T6 | Imports the same public interface; no adaptation. |

These are all modules reported by `tools/downstream.py` for the item. Its
`--uses CategoryTheory.roosF_homotopy_functor` search additionally confirms the
single direct theorem user, QuotientScalarComparisonDescent. Reading their
imports and uses confirms that neither their statements nor their proofs need
adaptation: only private constants and a theorem proof change. No target
statement or definition changes, so no target acquires a different meaning.

## Status

landed 20261021T120435-L-3895816 2026-10-21 (merge of deliver/N2/Sheaf.CategoryTheory.StrictRoosHomotopyFunctor)
