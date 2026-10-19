# CategoryTheory.coefMonoidalSquareHomTransport

## Reason

The static delivery check classifies new `variable` and `open` commands as a
possible interface change. This record documents their precise scope. They occur
inside the new `ComparisonProofs` section and support seven proved private helper
lemmas. All existing declaration signatures, definitions, public imports,
visibility, universes, and docstrings are unchanged. There are no added instances,
attributes, or notation. In particular no target meaning changes and no statement
review is reopened.

## Old

No `ComparisonProofs` section. After `SuccessiveCoefficientHomTransport` the file
proceeds directly to the docstring and declaration of
`coefMonoidalSquareHomTransport`.

## New

The following commands precede the seven private lemmas:

```lean
section ComparisonProofs

variable {C : Type uCA} [Category.{vCA} C] [MonoidalCategory C]
  {D : Type uCB} [Category.{vCB} D] [MonoidalCategory D]
  {E : Type uDA} [Category.{vDA} E] [MonoidalCategory E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]

open Category Functor.LaxMonoidal
```

The section ends with `end ComparisonProofs` before the existing public theorem.
The variables and namespace openings elaborate the private helpers only. A
proof-only import of
`WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic` supplies the existing
comparison API; it exposes nothing to importers of this module.

## Users

The `tools/downstream.py` scan found 418 downstream modules, including two direct
importers. Its `--uses` scan for all six existing declarations found only the item
module itself, and no downstream textual use. The two direct importers and all
416 indirect importers continue to see exactly the same existing declarations;
no consumer adaptation is necessary. No other group's module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.CoefMonoidalSquareHomTransport | V3 | Single public theorem proved using seven proved private helpers; signatures and definitions unchanged. |
| Sheaf.Paper.FiniteCoefficientHomChange | not edited | Proof-only importer; no declaration use and no adaptation. |
| Sheaf.Paper.GeometricFrobeniusInternalHomComparison | not edited | Proof-only importer; no declaration use and no adaptation. |

## Status

landed 20261019T112554-L-3956771 2026-10-19 (merge of deliver/V3/Sheaf.SixFunctors.CoefMonoidalSquareHomTransport)
