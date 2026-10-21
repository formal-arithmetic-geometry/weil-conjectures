# AlgebraicGeometry.Etale.essentiallySmall_etale_shriekTensorMain

## Reason

The proof of `compactSupportProjectionMap_comp` must use the same universe-sized
small-etale instance as the adopted derived-functor APIs. This supporting local instance
provides the canonical proof of `EssentiallySmall.{u + 1} X.Etale` from the standard
`LocallySmall` and small-category instances. `EssentiallySmall` is a proposition, so this
adds no mathematical data. The instance attribute is local to its proof section; the
named constant is public under the item's existing public section.

Both original public definition bodies, both theorem signatures, and all original public
imports remain verbatim apart from whitespace. No definition used by a target changes,
so no target meaning or statement-review obligation is reopened by this proof instance.
No source-library module is changed.

## Old

Absent. This is a new supporting instance, not a replacement definition or signature.

## New

```lean
local instance essentiallySmall_etale_shriekTensorMain (X : Scheme.{u}) :
    EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ShriekTensorComposition --uses
AlgebraicGeometry.Etale.essentiallySmall_etale_shriekTensorMain` finds one downstream module and zero references
to this new declaration in the shared sources. The current claims contain no claim for
that downstream module. No downstream adaptation is required.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ShriekTensorComposition | Q1 | New supporting local proof instance; original public interfaces preserved. |
| Sheaf.SmoothPurity.TensorMateEtalePrecomp | unclaimed | Imports the item; does not reference this new name. Statements and proofs need no adaptation. |

## Status

landed 20261021T005743-L-1888393 2026-10-21 (merge of deliver/Q1/Sheaf.AlgebraicGeometry.ShriekTensorComposition)
