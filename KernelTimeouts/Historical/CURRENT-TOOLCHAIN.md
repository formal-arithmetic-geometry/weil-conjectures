# Current-toolchain reproduction (Lean v4.35.0)

Date: 2026-11-20. Toolchain: Lean v4.35.0 (`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), current master `origin/master` at `08909ce7ec5ca53e05d5c90d325a137312206995`.

All commands used `timeout 3600`, `/usr/bin/time -v`, and at most `LAKE_JOBS=16`. Disk usage was watched throughout: it reached 85%, below the 88% stop threshold. The first Mathlib cache fetch failed because the process hit the server file-descriptor limit while decompressing already-cached files; the import-closure build then completed successfully from the partial cache. No library files were edited.

## Case B: Derived-completion cone

Probe: `KernelTimeouts/Historical/Current/Cone.lean`. It imports `WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs` and defines the inline/named and inferred/explicit-instance combinations B00/B10/B01/B11, each with a `sorry` value and the real cone value. A `run_cmd` separately calls `Kernel.check` on the declared type and value and `Kernel.isDefEq` on the inferred and declared types.

Measured phase timings (milliseconds, direct measurements from the probe):

| Variant | Type | Value | Final isDefEq |
|---|---:|---:|---:|
| B00 sorry, inline/inferred | 0 | 2 | 5 |
| B00 real, inline/inferred | 0 | 2 | 5 |
| B10 sorry, named/inferred | 0 | 0 | 0 |
| B10 real, named/inferred | 0 | 2 | 2 |
| B01 sorry, inline/explicit | 0 | 1 | 2 |
| B01 real, inline/explicit | 0 | 2 | 1 |
| B11 sorry, named/explicit | 0 | 1 | 0 |
| B11 real, named/explicit | 0 | 2 | 2 |

The complete probe process took 2.71s wall time and 3,702,724 kB maximum RSS. Diagnostics were enabled; inline variants showed additional reduction/kernel unfolding of `DerivedCategory.TensorStructure.monoidalCategory`, `DerivedCategory.sheafTensorStructure`, `DerivedCategory.tensorStructure`, `inferInstance`, and `Quiver.Hom`, while named variants avoided those large reductions. Every phase completed. **Reproduces on v4.35.0: no** (the historical timeout is not reproduced). The `sorry` rows are diagnostic controls and are not successful proofs.

Skip-kernel control (`-Ddebug.skipKernelTC=true`) also completed in 2.68s wall time with 3,701,992 kB maximum RSS, with B00/B10/B01/B11 final timings 4/0/2/0ms for `sorry` and 4/2/2/2ms for the real values. This control confirms the probe remains elaborable without kernel declaration checking; the ordinary runs above are the results used for reproduction.

## Case A: Slow derived tensor

Worktree: current master detached at `08909ce7ec5ca53e05d5c90d325a137312206995`; consumer: `WeilConjectures.SixFunctors.Etale.Derived.Tensor`.

Unchanged current-master baseline (the six declarations remain `@[reducible] def`):

- import-closure build: 3,559 jobs, 1:41.24 wall time, 1,774,560 kB maximum RSS;
- consumer `lake env lean`: 2.37s wall time, 1.92s user, 2,604,024 kB maximum RSS;
- target kernel probe: type 4ms, value 2ms, final conversion 2ms, 4,201,292 kB maximum RSS.
- skip-kernel consumer control: 2.35s wall time, 1.86s user, 2,603,720 kB maximum RSS.

Historical source change: only the six declarations `HasLeftDerivedFunctor₂/₃/₄` and `IsLeftDerivedFunctor₂/₃/₄` in `LeftDerivedTwo.lean`, `LeftDerivedThree.lean`, and `LeftDerivedFour.lean` were changed from `@[reducible] def` to `abbrev`, preserving bodies and consumer. The abbrev closure built successfully:

- import-closure build: 3,559 jobs, 2:21.38 wall time, 6,228,104 kB maximum RSS;
- consumer `lake env lean`: 60.90s wall time, 60.51s user, 7,067,956 kB maximum RSS;
- target kernel probe: type 5ms, value 1ms, final conversion 58,196ms, 8,649,180 kB maximum RSS.

For the target declaration, `Kernel.check(type)` and `Kernel.check(value)` stayed cheap, while final `Kernel.isDefEq` dominated. The declared type's outer application contains `AlgebraicGeometry.Etale.derivedTensor`; after the body is exposed, the inferred type contains `CategoryTheory.MonoidalCategory.curriedTensor`. This is direct expression inspection from the probe output. The timing supports a reducibility-sensitive comparison-boundary effect; the shared-head/argument comparison explanation is an interpretation, not a direct kernel trace.

Plain `def` (without `@[reducible]`) was also tested with the same bodies. It did not elaborate the closure on v4.35.0: the first error was `invalid binder annotation, type is not a class instance` at the `HasLeftDerivedFunctor₂` instance binder, followed by typeclass-synthesis and dependent declaration errors in `LeftDerivedTwo.lean` and `LeftDerivedFour.lean`. Therefore no timing is reported for A1.

Restored `@[reducible] def` after the abbrev run:

- import-closure rebuild: 3,559 jobs, 1:21.63 wall time, 1,776,168 kB maximum RSS;
- target kernel probe: type 4ms, value 2ms, final conversion 2ms, 4,201,292 kB maximum RSS.

**Reproduces on v4.35.0: yes.** The historical slowdown reproduces with `abbrev`; the current `@[reducible] def` workaround remains fast. The exact direct measurements are above. The A0/A2 conclusion is strong; A1 is an elaboration failure under the current toolchain rather than a comparable performance row.

## Sources and changes

- Cone probe source adaptation: current `Defs.lean` already uses the named diagram and local `sheafTensorStructure` instance. The probe only adds fresh names B00/B10/B01/B11 and explicit phase calls; no library source was changed.
- Tensor source adaptation: current master already uses `@[reducible] def`; the historical variant changes only declaration keywords to `abbrev`, then restores them. Plain `def` was tested as a scratch variant and failed elaboration.
- The tensor kernel probe uses the public declaration `AlgebraicGeometry.Etale.isLeftDerivedFunctor₂_derivedTensor`, retrieves its environment declaration, and times `Kernel.check` for type/value plus final `Kernel.isDefEq`.
