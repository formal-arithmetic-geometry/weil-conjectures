# Sheaf.RingTheory.ZariskisMainAway public imports

## Reason

Upstream review #1428 requested removal of the duplicate Zariski main wrapper.
The wrapper and its three callers were already repaired by Y3. The now empty
module still imports the project-specific fibre predicate it no longer uses. Prune that import,
completing the dependency cleanup without restoring the wrapper.

## Old

```lean
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Sheaf.RingTheory.QuasiFiniteAtPrime
```

## New

Only the Mathlib import remains, preserving the standard compatibility entry point.
There are no declarations, definitions or theorem
signatures in the module. The module docstring describes the retired wrapper
and direct use of Mathlib by its former callers.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.ZariskisMainAway | R4 | removes the unused Sheaf public import |
| Sheaf.RingTheory.QuasiFiniteIntegralClosureOpen | unclaimed | unchanged; compiles against the pruned module |

The latter is the sole remaining direct importer, with a private import. It
already publicly imports QuasiFiniteAtPrime and its other statement dependencies.
Its original source was copied temporarily into the sandbox and compiled in
import order against the edited module using lcompile.py --all (exit 0, no
warnings, 1.6 seconds for the importer). The temporary source was removed from
the delivery: no forced adaptation is necessary. No existing declaration or
visibility changes, and no target semantics change. The node already records
Mathlib's theorem and the caller-local conversion, so its proof route is unchanged.

## Status

landed 20261014T035546-L-888220 2026-10-14 (merge of deliver/R4/Sheaf.RingTheory.ZariskisMainAway)
