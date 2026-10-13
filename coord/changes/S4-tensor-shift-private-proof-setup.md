# AlgebraicGeometry.schemeTensorShift_targetComparison_isIso

## Reason

The static interface detector flags added universe and scoped `open`/`omit`
commands for two proved private helpers. No existing statement, definition,
visibility or instance changes. This record makes that proof setup reviewable.

## Old

```lean
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
```

All existing declarations and their signatures are retained verbatim.

## New

```lean
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
```

`open Functor.LaxMonoidal in` scopes names to the private, proved
`tensorator_isIso` theorem. A scoped `omit` removes the unused derived-category
parameter from private, proved `upstreamKFlat`. Neither helper occurs in any
public signature or definition. The proof of the existing invertibility theorem
uses them; all other public bodies and signatures are unchanged. A scoped
`set_option linter.unusedVariables false in` on this theorem preserves its
intentionally unused original hU binder without a warning.

## Users

The detector's changed-command marker names no public declaration used by a
consumer. Every downstream module has exactly the same public interface. No
consumer requires an adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization | S4 | Private proof setup and completed proof only; existing interfaces unchanged. |

## Status

landed 20261013T222415-L-1227118 2026-10-13 (merge of deliver/S4/Sheaf.AlgebraicGeometry.SchemeTensorShiftLocalizationNormalization)
