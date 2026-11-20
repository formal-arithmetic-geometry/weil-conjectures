# Instrumented Lean Kernels

These observational patches apply to the exact Lean release commits
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc` (4.35.0) and
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6` (4.33.1). Both
unpatched source and patched binaries report the corresponding release
`lean --githash`. The 4.35.0 patch covers `src/` and `stage0/src/`;
the 4.33.1 patch covers `src/`. Both patches passed `git apply --check`
against pristine release checkouts.

The validated builds used `-DCMAKE_BUILD_TYPE=Release -DUSE_MIMALLOC=ON`
and at most `-j24` per build. The 4.35.0 stage-0 build used the release's
pinned mimalloc v3.4.5; the 4.33.1 source build used v2.2.3. Fresh build
directories were essential after allocator changes: reconfiguring an old
non-mimalloc 4.35.0 directory produced a binary that crashed at runtime
initialization. The fresh source builds load the corresponding historical
and current-tree oleans. A worktree-based 4.33.1 baseline generated an
incorrect `githash.h` through CMake, so its generated header was set to
the release hash before relinking; the patch does not alter githash.

| Version | Unpatched source binary | Patched binary | Olean smoke |
| --- | --- | --- | --- |
| 4.35.0 | `build35-release-base/bin/lean` | `build35-release-cpp/bin/lean` | current-tree `KernelSmoke.lean` passed |
| 4.33.1 | `build33-release-base/bin/lean` | `build33-release-cpp/bin/lean` | rebuilt historical probes passed |

Set `KERNEL_ROOT` to the build directory's parent. In the current tree,
run `lake env bash "$KERNEL_ROOT/current-lean.sh"
"$KERNEL_ROOT/build35-release-cpp/bin/lean" <probe>`. In a historical
worktree, use `bash "$KERNEL_ROOT/run33.sh"
"$KERNEL_ROOT/build33-release-cpp/bin/lean" <probe>`. The wrappers
compute the project Lean path with Lake, then put that binary's
`lib/lean` first in `LD_LIBRARY_PATH`. Set
`LEAN_DEFEQ_ANATOMY=counters` or `trace` and
`LEAN_DEFEQ_MIN_MS=100` before the command. With the mode unset the
patched binary emits no anatomy report. Output goes to stderr as
`ANATOMY root=...`, followed by branch, depth/fan-out, proposition,
proof-position, Delta-head, and top-child lines where available.
`LEAN_DEFEQ_MIN_MS` filters printed roots by measured core duration;
root serials are process-local, not declaration IDs.

## Measured overhead

All times below are process wall on the same probe and import closure,
one target Lean thread. Slow controls compare counter/trace to unpatched
source; fast times are dominated by fixed startup/import work.

| Version and probe | Installed release | Source | Counters | Trace |
| --- | ---: | ---: | ---: | ---: |
| 4.35.0 `KernelSmoke.lean` | 1.32 s | 1.46 s | 1.48 s | 1.42 s |
| 4.35.0 NativePullTensor domain pair | 49.39 s | 50.52 s | 53.79 s (+6.5%) | 59.81 s (+18.4%) |
| 4.33.1 named-cone control | 2.39 s | 2.24 s | 2.15 s | 2.20 s |
| 4.33.1 Tensor argument 2 | 48.20 s | 47.42 s | 50.19 s (+5.8%) | 60.98 s (+28.6%) |
| 4.33.1 inline Cone timeout | 124.38 s | 115.96 s | 124.83 s (+7.6%) | 150.39 s (+29.7%) |

The 4.35.0 slow probe selected two domain conversions, both succeeding;
the 4.33.1 Cone consistently reached the deterministic kernel timeout.
Output and call-count equivalence were checked across baseline and
instrumented modes. Counter-mode exclusive comparison and outer-WHNF
times form a partition of the measured recursive root span. Delta timers
and nested-exclusive proposition timers overlap that partition. Detailed
pair capture is bounded at five million general recursive entries.

Limitations: no automatic declaration-name filter, full argument/field
path, context fingerprint, reverse-pair accounting, repeated-subtree
inclusive time, Expr allocation/bytes, or GC timer. Raw-expression
hashes are grouping proxies. The P and T current-case reports were
recorded with an earlier observational revision of the patch; the
final patches add cache and proposition-group diagnostics without
changing conversion behavior. Their recorded counters remain tied to
that earlier revision.
