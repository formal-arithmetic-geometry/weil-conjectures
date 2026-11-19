# PR #1743: supported restriction integral

`Before.lean` and `After.lean` are successful 4.35.0 prefixes ending after
`map_supportedRestrictionIntegral_comp`. The old proof is transplanted from the
merge parent of [PR #1743](https://github.com/formal-arithmetic-geometry/weil-conjectures/pull/1743),
with its historical import/API spelling; the fixed proof is the current one.
Both were run with `LEAN_NUM_THREADS=1`, `-DElab.async=false`, profiler threshold
50 ms, and `/usr/bin/time -v`. No `sorry` occurs in either file.

| Form | User CPU s | Wall s | Peak RSS KB | Tactic time | Kernel time |
|---|---:|---:|---:|---:|---:|
| Before | 579.86 | 580.90 | 3,729,204 | 572 s | 3.40 s |
| After | 10.09 | 11.08 | 3,550,928 | about 2 s | 3.89 s |

The old target has a 223 s `refine` and a 349 s `exact`. The historical PR
identifies the expensive matching of `σ.hom.app` against a named base-change
component, followed by a composite comparison at default transparency. The
fixed theorem states equality of the whole base-change morphisms and uses
`with_reducible exact` after unfolding the named constructions.
