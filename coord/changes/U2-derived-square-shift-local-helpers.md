# Local shift compatibility helpers in DerivedSquareIsoCommShift

## Reason

The proof needs shift compatibility for the exact-functor derived natural-isomorphism
and composition APIs. The pinned library provides their factorization equations and
homotopy-category shift instances, but does not register the derived comparison
compatibilities as instances. Two private theorems are therefore proved in the item
module and registered with a local `attribute [local instance]` command. They are
scoped to this module and do not add declarations or instances visible to importers.

## Old

The item module contained only the public theorem and its `sorry`; no local helper
lemmas or local instance attributes were present.

## New

The module contains private theorems `commShift_derivedPlusNatIso` and
`commShift_derivedPlusCompIso`, plus a local instance attribute for them. The theorem
signatures and all public declarations remain unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedSquareIsoCommShift | U2 | Uses the private helpers to prove the assigned theorem. |
| All downstream modules | none | No effect: helpers and the instance attribute are private/local. |

## Status

landed 20261018T062924-L-683486 2026-10-18 (merge of deliver/U2/Sheaf.AlgebraicGeometry.DerivedSquareIsoCommShift)
