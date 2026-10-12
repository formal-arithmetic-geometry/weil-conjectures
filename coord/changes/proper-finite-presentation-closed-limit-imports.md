# ProperFinitePresentationClosedLimit proof imports

## Reason

The new proof constructs the ideal-sheaf approximation directly from a proper envelope.
The old private proof imports are unused. The original public imports are unchanged, and
no existing signature or definition changes. This record documents the import removal
required by the delivery preflight.

## Old

```lean
import Sheaf.AlgebraicGeometry.ChowFiniteType
import Sheaf.AlgebraicGeometry.EventuallyClosedImmersion
import Sheaf.AlgebraicGeometry.NagataFinitePresentationEnvelope
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
```

## New

```lean
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimitEnvelope
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimit | C1 | proof imports changed |
| Sheaf.AlgebraicGeometry.ProperLimitNoetherian | none recorded | unchanged signature and public imports; no adaptation needed |

## Status

landed 20261012T053922-L-2631044 2026-10-12 (merge of deliver/C1/Sheaf.AlgebraicGeometry.ProperFinitePresentationClosedLimit)
