# AlgebraicGeometry.ProEtale.CondensedRing.tensorClosureRational

## Reason

The proof needs tensor notation and must keep large categorical constructions from
unfolding during elaboration. Open `MonoidalCategory` and mark three existing
constructions locally irreducible. These commands apply within this module. The
preflight conservatively classifies the command changes as an interface change and
requires this record. The theorem retains its exact signature and public imports;
its proof now uses two proved private helpers and a new, proved coefficient-transport
lemma in its own module.

## Old

```lean
@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
```

## New

```lean
@[expose] public section

attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
```

The new module `Sheaf.SixFunctors.ConstructibleCoefficientTransport` declares the
proved theorem `AlgebraicGeometry.ProEtale.CondensedRing.constructibleCoefficientTransport`;
its full statement is recorded by `lem-sf-constructible-coefficient-transport`. It is
imported only for the item's proof. All other added declarations are private proved
helpers. No existing definition changes, so no target statement changes meaning.

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.FieldTensor --uses tensorClosureRational`
lists the eight transitive consumers below. The only textual occurrence of the
theorem name is its own declaration. In particular no consumer needs to change its
signature, definition or proof. The two direct consumers import this module privately.
The local attribute and namespace-opening commands do not export changes to them.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstructibleFiniteTorAdjunctions | C6 | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.RationalLocalizingProjectionFormula | U4 | Same public declarations and imports; no adaptation. |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | Same public declarations and imports; no adaptation. |
| Sheaf.SecSmoothPurity.MixedBaseChange | Z8 | Same public declarations and imports; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Same public declarations and imports; no adaptation. |
| Sheaf.SixFunctors.CtfStabilityDirectImages | J6 | Same public declarations and imports; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Same public declarations and imports; no adaptation. |

## Status

landed 20261019T112501-L-3944951 2026-10-19 (merge of deliver/N1/Sheaf.SixFunctors.FieldTensor)
