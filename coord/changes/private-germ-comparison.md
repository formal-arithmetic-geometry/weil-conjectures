# Private GermComparison proof context

## Reason

The delivery adds private proved helpers in a closed namespace and sections.
The interface scanner conservatively flags their scoped `variable`, `omit`,
`section` and `open scoped` commands as an interface change. No existing
signature, definition, public import, notation or global attribute changes.
The proof-only imports and private declarations are inaccessible to importers.

## Old

```lean
universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale
```

## New

```lean
universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

namespace GermComparison

section LocalComparison

variable {C : Type (v + 1)} [Category.{v} C]
  {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{v + 1}]
```

The remaining context commands bind the derived-category, sheaf-composition,
K-injective and enough-injectives hypotheses of private helpers. All sections
and the `GermComparison` namespace end before the unchanged public theorem.
The existing public theorem has exactly its old signature and a completed proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedCohomologyGermIso | D3 | Private proof context only; public theorem unchanged. |

`tools/downstream.py Sheaf.AlgebraicGeometry.DerivedCohomologyGermIso` lists no
additional downstream users for this conservative command-only change.
No target definition or signature changes and no adaptation is required.

## Status

landed 20261012T112833-L-765603 2026-10-12 (merge of deliver/D3/Sheaf.AlgebraicGeometry.DerivedCohomologyGermIso)
