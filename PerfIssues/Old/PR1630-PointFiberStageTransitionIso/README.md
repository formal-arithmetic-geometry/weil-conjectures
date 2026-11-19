# PR #1630: point-fiber stage transition

`Before.lean` restores the old `pointFiberStageTransitionIso` value on the
current module prefix. `After.lean` is the current value on that same prefix.
Both full files compile with the original module identity and Lake setup on
Lean 4.35.0. The [PR](https://github.com/formal-arithmetic-geometry/weil-conjectures/pull/1630)
also changes two earlier declarations; this pair isolates its final change.
Runs used `LEAN_NUM_THREADS=1`, `-DElab.async=false`, profiler threshold 50 ms,
and `/usr/bin/time -v`. No `sorry` occurs.

| Form | User CPU s | Wall s | Peak RSS KB | Largest target `exact` | Kernel total |
|---|---:|---:|---:|---:|---:|
| Before | 185.07 | 185.80 | 2,624,356 | 84.8 s | 8.88 s |
| After | 92.14 | 92.85 | 2,516,012 | under 50 ms | 7.08 s |

The old value constructs component isomorphisms and proves naturality by
`ext; exact β.hom.naturality f`. The fixed value constructs an isomorphism of
the composed functors and pulls it back through fully faithful whiskering
with `preimageIso`. Earlier current-prefix elaboration remains in both files.
