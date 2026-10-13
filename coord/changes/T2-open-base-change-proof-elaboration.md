# Open base-change proof elaboration

## Reason

The static delivery check classifies new local attributes and elaboration options as
interface commands. This record documents their scope. No existing statement,
definition, public import or exported attribute changes. The local controls prevent
expensive unfolding during the proved mate calculation and let it compile within
the unchanged 60-second limit.

## Old

The module had `set_option autoImplicit false`, the existing universe and namespace
commands, and the original theorem with `:= by sorry`. It had no local irreducibility
attributes or transparency options for this calculation.

## New

The original theorem has its identical signature and a complete proof from two
smaller named statements. Added file-local commands are:

```lean
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] derivedPullback singleComplexOpenDirectImageIso
  singleComplexOpenPullbackIso CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor singleComplexRestrictedCoefficient
  singleComplexOpenBaseChangeSourceIso singleComplexOpenPullbackSquareIso
  schemeDerivedBaseChangeMap singleComplexOpenSquareComparison
attribute [local irreducible] CategoryTheory.Adjunction.homEquiv
```

The theorem also uses a local `maxHeartbeats` option. These affect elaboration in
this module only, and are not exported. No other existing module is edited.

## Users

The direct declaration users identified by tools/downstream.py are listed below.
Both keep compiling against the same statement and visibility; no adaptation is
needed. New private helpers do not enter their signatures.

| Module | Current holder | Effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroTarget | unclaimed | Signature and visibility unchanged; proof-local settings have no effect. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeIdentity | unclaimed | Signature and visibility unchanged; proof-local settings have no effect. |

## Status

landed 20261013T161321-L-1424247 2026-10-13 (merge of deliver/T2/Sheaf.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation)
