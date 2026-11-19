# ScalarModelRoosZeroLiftFactorizationFromCoordinates

Lean 4.35.0 with built Mathlib, master build revision `1ef1fddac73e`, one Lean thread, `nice -n 10`, synchronous elaboration. The handover estimated 687 whole-module CPU seconds by instruction count. The unchanged whole source is **not a valid completed baseline**: it exits 1 after 303.18 s wall, 302.30 s user CPU, 0.91 s system CPU, and 2,783,076 KB peak RSS, with `simp made no progress` at line 182 (a type mismatch involving a cast between two coefficient-restriction objects). Its first private theorem succeeds before that error.

The probes end immediately after `scalarCounit_natural`, the valid first theorem, and close the namespace:

| Run | Wall s | User CPU s | System CPU s | Peak RSS KB | Result |
|---|---:|---:|---:|---:|---|
| [CounitPrefix.lean](probes/CounitPrefix.lean), Kernel on | 295.17 | 294.31 | 0.87 | 2,784,552 | success |
| Same prefix, Kernel skipped | 296.07 | 295.22 | 0.86 | 2,755,624 | diagnostic success |
| [CounitSorry.lean](probes/CounitSorry.lean), Kernel on | 2.92 | 2.12 | 0.82 | 2,723,976 | diagnostic warning |

The per-declaration profiler assigns 292 s to the sole `Lean.Parser.Tactic.exact` in `scalarCounit_natural`, while checking its proof term takes 0.404 s. The full failing run shows the same 292 s `exact` and 0.404 s type check before its later error. Replacing that block with `sorry` cuts the valid prefix to 2.92 s.

Command form from the master build tree (replace `SOURCE`):

```sh
LEAN_NUM_THREADS=1 timeout 900 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 SOURCE
```

The skipped control adds `-Ddebug.skipKernelTC=true`. Neither the failed whole module nor a diagnostic control is counted as a successful whole-module compile.

## Round 3 controls on the valid prefix

All variants preserve the imports and theorem context, use one Lean thread and
the same synchronous command, and stop after the first theorem. CPU times are
whole-prefix user seconds. A trace adds its own printing overhead.

| Probe | User CPU s | Result |
|---|---:|---|
| [CounitNoUnfold.lean](probes/CounitNoUnfold.lean), same `exact` without wrapper | 294.28 | success; wrapper not needed for slow path |
| [CounitHaveWitness.lean](probes/CounitHaveWitness.lean), opaque named `have` | 14.44 | type mismatch at goal; no valid speedup |
| [CounitLetWitness.lean](probes/CounitLetWitness.lean), transparent `let` | 295.95 | success; still slow |
| [CounitTransparencyTrue.lean](probes/CounitTransparencyTrue.lean) | 297.65 | success |
| [CounitTransparencyFalse.lean](probes/CounitTransparencyFalse.lean) | 294.57 | success |
| [CounitAbstract.lean](probes/CounitAbstract.lean), generic local-variable lemma | 2.31 | abstract lemma succeeds; concrete theorem replaced by diagnostic `sorry` |
| [CounitDiagnostics.lean](probes/CounitDiagnostics.lean) | 297.42 | success; 1 s diagnostics threshold |
| [CounitProfilerOnly.lean](probes/CounitProfilerOnly.lean) | 303.46 | success; slow nested Meta nodes retained |

Diagnostics of the slow call count 25,076 `sheafCompose`, 22,328
`Classical.indefiniteDescription`, 20,624 `Classical.choose`, 20,448
`presheafToSheaf`, and 249,887 reducible `Functor.obj` unfolds. These are
workload counters, not individually timed causes. The filtered profiler finds
a 285.339-second `Meta.isDefEq` node, with 187.936 and 97.401-second children;
the deepest repeated `ε.1` comparisons take 89.070 and 88.206 seconds.

Setting `trace.Meta.isDefEq true` explicitly overrides the profiler threshold
in Lean's trace machinery and emits tiny nodes as well, so the bounded trace
uses `trace.profiler true` and `trace.profiler.threshold 2000` without enabling
the class. The named `have` introduces an opaque local whose `witness.app`
does not definitionally match the goal's chosen witness. Its early failure is
not a successful alternative proof. The abstract probe explicitly marks its
concrete theorem with `sorry`; only its generic lemma timing is meaningful.
