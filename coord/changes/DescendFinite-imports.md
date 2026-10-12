# Sheaf.AlgebraicGeometry.DescendFinite imports

## Reason

The unused public import of LimitAffineTransition is unnecessary for the existing
signature. DescendAffine privately supplies the affineness descent proof. Removing
the public import follows the stage-3 requirement to prune unused imports.
No existing declaration, definition, or target statement changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LimitAffineTransition
```

## New

The import is removed; the remaining public Mathlib imports supply the signature.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DescendFinite --uses
exists_limit_affine_transition` reports 200 downstream modules and zero uses of the
only declaration of LimitAffineTransition. The four direct importers are listed
below. Each independently imports the upstream AffineTransitionLimit module, so
its Mathlib declarations remain available. Two also import LimitAffineTransition
directly. No caller requires adaptation; no target meaning changes.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingLimitDescent | E2 | Has its own LimitAffineTransition import; no effect |
| Sheaf.AlgebraicGeometry.DescendFiniteLocallyFree | unclaimed | Has its own upstream AffineTransitionLimit import; no effect |
| Sheaf.AlgebraicGeometry.FiniteSurjectiveAffineTarget | unclaimed | Has its own LimitAffineTransition import; no effect |
| Sheaf.AlgebraicGeometry.FiniteEtaleLiftingApproximation | C2 | Has its own upstream AffineTransitionLimit import; no effect |

## Status

landed 20261012T053929-L-2634410 2026-10-12 (merge of deliver/F2/Sheaf.AlgebraicGeometry.DescendFinite)
