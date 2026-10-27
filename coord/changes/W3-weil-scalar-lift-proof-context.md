# Weil scalar lift proof elaboration

## Reason

Complete the associator lift without changing any public interface. Profiling
found large expanded scalar-localization category and linear structures during
elaboration. Local irreducibility annotations keep those structures folded and
have no exported attribute effect. No definition data, mathematical statement,
target type, public import, public instance, or global attribute changes.
No transparency or time limit is relaxed.

## Old

The existing coefficient-specific irreducibility annotations remain verbatim.
There was no additional local irreducibility annotation for the generic
scalar-localization category and linear structures.

## New

The item additionally uses this local elaboration boundary:

```lean
attribute [local irreducible] ScalarLocalization.category ScalarLocalization.preadditive
  ScalarLocalization.composition ScalarLocalization.linear ScalarLocalization.linearOriginal
  AlgebraicGeometry.Scheme.pbcIntegralLinear AlgebraicGeometry.Scheme.pbcCompletedDerivedLinear
  AlgebraicGeometry.Scheme.pbcCompletedModulesLinear
```

All existing public signatures and definition bodies remain unchanged. In
particular, the noetherian instance and coefficient-hypotheses proof bodies are
preserved verbatim. The annotations apply only while elaborating this module.

## Users

There is no changed public signature, definition, or exported attribute.
Importers retain the same interface and require no adaptation. The earlier
return's tensor universe error is already repaired in the current tensor source;
this packet does not repeat the noetherian instance change from that old delivery.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PbcWeilCategory | W3 | Complete its associator theorem with locally folded coefficient data. |

## Status

landed 20261026T003105-L-145415 2026-10-26 (merge of deliver/W3/Sheaf.Paper.PbcWeilCategory)
