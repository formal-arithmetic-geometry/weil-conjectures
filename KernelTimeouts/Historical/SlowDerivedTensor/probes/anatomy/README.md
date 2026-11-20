# Slow Derived Tensor anatomy probes

Use the Lean 4.33.1 historical worktree at `bdab171985a`, Mathlib at
`0df444a360eaa60ab8c11dca51a86af692955474`, and a rebuilt
`WeilConjectures.SixFunctors.Etale.Derived.Tensor` import closure.
The same `standalone.lean` probe also runs against fixed revision
`428569e1ce1` after rebuilding that revision's targeted import closure;
there it measures the fast full consumer and still-slow standalone pair.

`standalone.lean` runs the standalone and full-consumer forward/reverse
conversions. `instance.lean` runs the standalone instance comparison and
its application arguments. `argument2.lean` runs only the expensive
`MonoidalCategory` argument pair.

From the historical worktree, set `KERNEL_ROOT` to the instrumented-build
directory and run, for example:

```sh
LEAN_DEFEQ_ANATOMY=trace LEAN_DEFEQ_MIN_MS=100 \
  bash "$KERNEL_ROOT/run33.sh" "$KERNEL_ROOT/build33-release-cpp/bin/lean" \
  -Dbackward.isDefEq.respectTransparency=false -DmaxSynthPendingDepth=3 \
  -Dwarn.sorry=false /path/to/probes/anatomy/argument2.lean
```

Use `LEAN_DEFEQ_ANATOMY=counters` for the lower-overhead aggregate. The
runner resolves Lake's package path before selecting the build's shared
library. The installed release binary or `build33-release-base/bin/lean`
is the uninstrumented baseline.
