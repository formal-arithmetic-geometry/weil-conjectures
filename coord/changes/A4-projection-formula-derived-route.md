# Local elaboration aliases for projection formula

## Reason

The projection formula proof repeatedly synthesizes the large canonical derived
monoidal structure. Local aliases keep elaboration below the 60-second limit.

## Old

The module synthesized `Mod.derivedMonoidalCategory` directly at every tensor
use and had no local aliases. The naturality theorem remained `sorry`.

## New

The module has local noncomputable aliases `projectionMonoidal` and
`projectionTensorData`, plus local irreducibility attributes for the two derived
functor definitions. It proves
`boundedConstructibleExceptionalProjectionMorphism_natural_right` by
`ObjectProperty.hom_ext` and ambient compactification naturality.

## Users

| module | current holder | changes |
| --- | --- | --- |
| WeilConjectures.PoincareDuality.ProjectionFormula | A4 | Local elaboration aliases and one proof body only. |

No other module is adapted and no public theorem signature changes.

## Status

landed 20261017T070004-L-916969 2026-10-17 (merge of deliver/A4/WeilConjectures.PoincareDuality.ProjectionFormula)
are local to this module; the earlier public cache declarations were removed
after the stage-3 gate rejected them.
