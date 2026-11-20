# Derived-Completion Cone anatomy probes

Use the Lean 4.33.1 historical worktree at `9ba4d01f55c`, Mathlib at
`0df444a360eaa60ab8c11dca51a86af692955474`, and a rebuilt
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` import closure.

`inline.lean` is the timeout reproduction. `named.lean`,
`explicit-instance.lean`, and `matrix.lean` are the three controls.
From the historical worktree, set `KERNEL_ROOT` to the instrumented-build
directory and run:

```sh
LEAN_DEFEQ_ANATOMY=counters LEAN_DEFEQ_MIN_MS=100 \
  bash "$KERNEL_ROOT/run33.sh" "$KERNEL_ROOT/build33-release-cpp/bin/lean" \
  -Dbackward.isDefEq.respectTransparency=false -DmaxSynthPendingDepth=3 \
  /path/to/probes/anatomy/inline.lean
```

Use `LEAN_DEFEQ_ANATOMY=trace` for pair and child detail. The runner
resolves Lake's package path before selecting the build's shared library.
The installed release binary or `build33-release-base/bin/lean` is the
uninstrumented baseline. The inline declaration uses `sorry` only to
isolate the final Kernel conversion; it is not a proof.
