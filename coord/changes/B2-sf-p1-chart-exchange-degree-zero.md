# SfP1Transport.chartExchange degree-zero interface repair

## Reason

Restore the quarantined item and adapt its existing complete proof to X7's cached
single-functor object interface. The old local irreducibility of the single functor
hides its new explicit ordinaryFiniteDegreeZero object field. The shifted comparison
then fails to elaborate, and unfolding only ordinaryFiniteDegreeZero in the composition
calculation produces inconsistent object normal forms.

## Old

```lean
attribute [local irreducible] upperStar lowerStar Scheme.finiteEtaleTateLine
  DerivedCategory.singleFunctors
  ordinaryFiniteSingleFunctor ordinaryFiniteSinglePullbackIso
  ordinaryFiniteSingleExactPullbackIso

attribute [local implicit_reducible] ordinaryFiniteDegreeZero
```

The shiftedLine_comp proof unfolded ordinaryFiniteDegreeZero directly in its
normalization and conversion steps.

## New

```lean
attribute [local irreducible] upperStar lowerStar Scheme.finiteEtaleTateLine
  DerivedCategory.singleFunctors
  ordinaryFiniteSinglePullbackIso
  ordinaryFiniteSingleExactPullbackIso

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
```

A proved private singleFunctor_obj equation rewrites just the object projection to
ordinaryFiniteDegreeZero. The shiftedLine_comp normalizations use this equation and
retain the named degree-zero object. Before the final comparison, expand shifted line
transport and normalize the cached functor projection explicitly on both sides. Public signatures, definition bodies, instances,
attributes and imports are preserved. All elaboration attributes changed here are local.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SfP1ChartExchange | B2 | Restore and repair local proof elaboration |
| Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransport | unclaimed | Public interface unchanged |
| Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportFalse | Q4 | Public interface unchanged |
| Sheaf.AlgebraicGeometry.SfP1ProjectionTraceTransportTrue | R1 | Public interface unchanged |

These are the direct importers in the live and quarantined source trees. Their
quarantined sources are preserved; this packet does not restore or adapt them.
All three direct importers compile unchanged against the repaired item in a single
lcompile.py set (30.0 s, 29.7 s and 30.2 s respectively for false, true and the
combined statement); the item compiled in 50.7 s in that set. Temporary unchanged
importer copies were then removed. No shared mathematical definition changes, and no
target meaning review is reopened.

## Status

landed 20261026T180627-L-3368754 2026-10-26 (merge of deliver/B2/Sheaf.AlgebraicGeometry.SfP1ChartExchange)
