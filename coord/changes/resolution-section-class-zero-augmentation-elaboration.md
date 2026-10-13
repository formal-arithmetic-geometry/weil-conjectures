# ResolutionSectionClassZeroAugmentation elaboration settings

## Reason

The original proof compiled with `lcompile.py` but exceeded the delivery wrapper's
60-second single-file limit. The expensive step is the degree-zero sheafification
comparison. Section-local irreducibility prevents unfolding the homology comparison
definitions during that private proof and keeps the public interface unchanged.

## Old

The private `theta_zero` section had no local irreducibility attributes.

## New

Within the private section only:

```lean
attribute [local irreducible] ShortComplex.mapHomologyIso ShortComplex.mapCyclesIso
  ShortComplex.homologyMap
```

The attribute scope ends before the public theorem.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ResolutionSectionClassZeroAugmentation | U2 | private elaboration setting only; no declaration signature or definition changes |

## Status

landed 20261013T130752-L-3987134 2026-10-13 (merge of deliver/U2/Sheaf.AlgebraicGeometry.ResolutionSectionClassZeroAugmentation)
