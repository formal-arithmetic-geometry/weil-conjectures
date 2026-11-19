# PR #2122: finite-etale integral boundary

`Before.lean` is the 733-line merge-parent module from
[PR #2122](https://github.com/formal-arithmetic-geometry/weil-conjectures/pull/2122).
`After.lean` is the current 133-line module. The fix moved common arguments
into separately compiled helpers, so these are same-name module compilation
costs with different imported dependency work; they are not isolated proof
value substitutions. Both compile on Lean 4.35.0 using the generated Lake
setup, `LEAN_NUM_THREADS=1`, `-DElab.async=false`, profiler threshold 50 ms,
and `/usr/bin/time -v`. Neither file contains `sorry`.

| Form | User CPU s | Wall s | Peak RSS KB | Kernel total |
|---|---:|---:|---:|---:|
| Before | 347.37 | 350.32 | 16,321,824 | 269 s |
| After | 29.87 | 30.69 | 5,285,748 | 27.2 s |

The old module has three checks of 15.6, 64.3, and 176 seconds; the final
theorem is the largest. The current module's one visible check is 27.2 seconds.
The historical fix names categories and comparison propositions, factors out
a generic Kummer argument, and splits the module.
