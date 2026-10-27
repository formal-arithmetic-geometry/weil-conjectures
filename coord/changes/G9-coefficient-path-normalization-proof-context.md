# AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarPathIso_eq_derivedPullIso_symm proof context

## Reason

Restore the returned item and its DAG attachment after its removal from the library.
The current shared snapshot contains no item source or quarantine archive; the full
retained sandbox proof supplies the restoration, with the original public signature.

The proof adds private categorical helpers and local elaboration commands to compare
specified derived counits and units. Preflight requires a change record for the
additional commands. The public theorem statement and its existing public import
are unchanged; no definition or target meaning changes.

## Old

```lean
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor derivedPullIso
  coefficientScalarPathIso internalScalarMonoidal
```

The theorem body was `by sorry` and had no private categorical helper declarations.

## New

```lean
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory upperStarFromPoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor derivedPullIso
  coefficientScalarPathIso internalScalarMonoidal upperStar lowerStar
  Functor.leftDerivedFunctorCounit Functor.rightDerivedFunctorUnit
  Functor.leftDerivedFunctorCompIso Functor.leftDerivedFunctorNatIso
  Functor.mapHomotopyCategory Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactorsh
  Mod.extendScalars Mod.comap
```

The following proof imports are private:

```lean
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit
```

The proof enables `backward.defeqAttrib.useBackward` locally to the module and
supplies the four exact-counit `IsIso` arguments directly to `asIso`, avoiding broad
instance search. Redundant local scalar monoidal instances were removed.

Private proved helpers handle localization, composition normalization, homotopy
comparison maps and the derived right-unit square. The heartbeat setting is scoped
to the unchanged public theorem. The local attributes keep large constructions
abstract during elaboration; they introduce no exported notation or instances.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoefficientPathNormalization | G9 | Same public statement; proof completed. |
| Sheaf.Paper.CoefficientProjectionSquare | unclaimed | Uses unchanged theorem; no adaptation required. |

The parent DAG proof now explicitly records the restored left-path normalization
as the link from the independent scalar tensor path to the specified pull comparison.
The parent statement and Lean source are unchanged.

The current local claims directory contains no claim for the consumer. Its source
copyright records Q07 as its author. No consumer module is modified.

## Status

landed 20261024T014955-L-2306601 2026-10-24 (merge of deliver/G9/Sheaf.Paper.CoefficientPathNormalization)
