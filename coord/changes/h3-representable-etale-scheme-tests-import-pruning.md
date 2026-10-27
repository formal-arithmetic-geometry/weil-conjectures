# AlgebraicGeometry.AlgebraicSpace.representable_etale_scheme_tests

## Reason

The proof uses Mathlib relative representability and its morphism-property calculus.
The statement's pullbacks are sheaf pullbacks. Proving their projections representable
étale or surjective does not require proving that their source is an algebraic space.
The public import of AlgebraicSpaceFibreProductsEtaleCovers is therefore unnecessary.
The item's public theorem signature and every definition remain unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
```

## New

The unused public import above is removed. Proof imports added:

```lean
import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.AlgebraicGeometry.PullbackCarrier
```

The unused private imports Mathlib.CategoryTheory.Yoneda,
Mathlib.AlgebraicGeometry.OpenImmersion,
Mathlib.AlgebraicGeometry.Sites.MorphismProperty, and
Mathlib.CategoryTheory.Limits.MorphismProperty are removed.
All other public imports are retained verbatim.
The new helpers and base-change instances are private and fully proved.

## Users

`python3 tools/downstream.py
Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests
--uses representable_etale_scheme_tests` reports zero downstream modules;
the only named occurrence is the declaration in the item itself.
A separate source search confirms no Lean importers of the item.
DAG parents still use the same theorem statement, with no adaptation needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests | H3 | Same public theorem signature; proof completed; unused imports removed. |

No source-library module, target, definition, or consumer is changed.

## Status

landed 20261023T123551-L-1212247 2026-10-23 (merge of deliver/H3/Sheaf.AlgebraicGeometry.AlgebraicSpaceRepresentableEtaleSchemeTests)
