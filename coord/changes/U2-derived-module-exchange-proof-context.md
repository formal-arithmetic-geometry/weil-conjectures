# AlgebraicGeometry.Etale.derivedExchangeModuleTermwise

## Reason

The static preflight classifies the new proof elaboration commands as a possible interface
change and requires this record. The theorem signature, public imports and the three existing
canonical-map definitions are verbatim unchanged. Fully proved private lemmas reduce the
homotopy-model exact-derived mate identity to the cochain representatives. Local irreducibility
keeps the generic proof calculations from expanding the large sheaf and localization functors.
The transparency options control elaboration only; they do not change the kernel statements.

## Old

No proof-context options or local irreducibility attributes after the public-section command.
The existing theorem body was exactly:

```lean
:= by
  sorry
```

## New

The new elaboration commands, verbatim, are:

```lean
set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
```

Inside `namespace AlgebraicGeometry.Etale`:

```lean
attribute [local irreducible] upperStar lowerStar squareUpperStarIso
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors Functor.mapDerivedCategoryFactorsh
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit Functor.rightDerivedFunctorUnitQ
  Functor.rightDerivedFunctorObjQIso
  Functor.mapDerivedCategoryNatIso Functor.mapDerivedCategoryCompIso
```

The local attributes end with the namespace. All six new helper theorems are private and
proved. No private helper appears in a public signature or a public definition body. The
existing theorem now has the complete proof in the accompanying module, using those helpers.
The three added imports are proof-only: `MapDerivedCategoryMate`, `DerivedExactMate`, and
`RightDerivedFunctor.ShortExactPullback` in their recorded namespaces. Eight unused proof
imports are removed, as listed in the report. No global attribute or instance is added.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DerivedExchangeModuleTermwise | U2 | One theorem proved; public signatures and definitions unchanged. |

`tools/downstream.py Sheaf.AlgebraicGeometry.DerivedExchangeModuleTermwise` reports zero
source consumers. A source search for each of the four original declaration names finds
only this module. Its DAG parents can use exactly the original interface; no parent or
consumer adaptation is required. No target statement or definition changes meaning.

## Status

landed 20261023T135449-L-2901297 2026-10-23 (merge of deliver/U2/Sheaf.AlgebraicGeometry.DerivedExchangeModuleTermwise)
