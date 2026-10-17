# formalSecondIdealQuotient_supported

## Reason

The proof no longer uses the Currying module. Its former public import exposed an
unneeded dependency to downstream modules, so it is removed as a proof-only pruning
change. The theorem declaration and all public signatures remain unchanged. The returned
duplicate helpers are removed and replaced by proof-only imports of existing
proved helpers; this does not change the public interface.

## Old

```lean
public import Mathlib.CategoryTheory.Functor.Currying
```

## New

The import is removed. No replacement import is needed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.GrothendieckDevissageSecondAdicSystemLiftData | unclaimed | Its import graph no longer receives the unused Currying module; its theorem use of `formalSecondIdealQuotient_supported` and all signatures are unchanged. |

The direct consumer was compiled unchanged against the repaired module in the
sandbox overlay; it passes. No consumer adaptation is needed.

## Status

landed 20261017T003426-L-3316873 2026-10-17 (merge of deliver/P2/Sheaf.AlgebraicGeometry.FormalSecondIdealQuotientSupported)
