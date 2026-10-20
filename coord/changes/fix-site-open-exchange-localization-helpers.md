# fixSiteOpenExchange localization helpers

## Reason

The proof needs local exactness instances for composition and local category variables
for the bounded-below face calculation. The interface scanner reports these scoped
commands as a visible change. All existing public signatures, definitions and imports
are preserved. The new helper definition and theorem are private.

## Old

No `Localization` helper section existed between `fixSitePullbackComparison` and
`fixSiteOpenExchange`. The theorem had `:= by sorry`.

## New

A `section Localization` declares private `derivedFace` and `derivedPlusFace`, using:

```lean
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
```

The section ends before the unchanged theorem signature. The theorem is proved by
`Functor.mapDerivedCategory_exactCube` and the ordinary sheaf comparison equation.
No existing definition body or elaborated signature changes. The two backward-defeq
options affect elaboration only; no instance or notation escapes the helper section.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.CompactSupportOpenFactor | unchanged; not adapted | Existing public declarations and imports unchanged |
| Sheaf.Paper.CompactSupportExchangeTransport | unchanged; not adapted | Existing public declarations and imports unchanged |
| Sheaf.Paper.EtaleCompactSupportCoefficientChange | unchanged; not adapted | Existing public declarations and imports unchanged |

## Status

landed 20261020T051348-L-1652640 2026-10-20 (merge of deliver/H3/Sheaf.AlgebraicGeometry.FixSiteOpenExchange)
