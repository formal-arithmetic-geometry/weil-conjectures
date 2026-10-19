# IntegralModelsOperations proof context

## Reason

The completed proof adds private helpers, opens Limits, and marks monoidal and
inverse-image constructions locally irreducible while elaborating this file.
The static interface checker records these command changes. All existing public
signatures, definitions, universes, visibility and public imports are unchanged.
The added imports are proof-only. No target meaning changes, no global instance
or notation is added, and no consumer needs adaptation.

The five new constituent modules contain complete proofs and are imported only
for the parent proof. Their public theorem statements and nodes are recorded in
the delivery. No existing definition is repaired or replaced.

## Old

Original command context outside declarations, excluding imports and comments:

```lean
module
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
end AlgebraicGeometry.ProEtale.CondensedRing
```

The existing declaration is
`AlgebraicGeometry.ProEtale.CondensedRing.integralModelsOperations`.
Its entire signature is retained verbatim; its original proof was `by sorry`.

## New

Delivered command context outside declarations, excluding imports and comments:

```lean
module
@[expose] public section
set_option autoImplicit false
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars
  AlgebraicGeometry.ProEtale.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.lowerStar
  AlgebraicGeometry.ProEtale.CondensedRing.openImmersionLowerShriek
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
end AlgebraicGeometry.ProEtale.CondensedRing
```

Every new helper in this existing module is private and proved. The existing
public theorem has the identical signature and a complete proof of all four
clauses. Local irreducibility changes elaboration here and does not change any
construction or the environment seen by importers. Kernel checking remains on.

## Users

`tools/downstream.py Sheaf.Paper.IntegralModelsOperations --uses
integralModelsOperations` found two external modules using the declaration.
The command-only interface flag names no changed declaration. The public import
closure and every original declaration are preserved, so all 338 downstream
modules retain their existing API. No downstream source is adapted.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.IntegralModelsOperations | N1 | Original signature unchanged; theorem proved. |
| Sheaf.SixFunctors.IntegralComplementFiniteness | unclaimed | Same theorem and public imports; no adaptation. |
| Sheaf.SixFunctors.IntegralRestrictionClosed | unclaimed | Same theorem and public imports; no adaptation. |

## Status

landed 20261019T192808-L-1868905 2026-10-19 (merge of deliver/N1/Sheaf.Paper.IntegralModelsOperations)
