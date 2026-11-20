# READY2 observational kernel patch

The `lean-v4.33.1-ad.patch` and `lean-v4.35.0-ad.patch` files extend the
earlier anatomy patches at the exact Lean release commits. The 4.35.0 patch
contains both `src/` and `stage0/src/` changes; its stage-0 changes are Git
binary patch records, so apply it with `git apply`. Both patches passed
`git apply --check` against pristine release checkouts. Builds used Release
and mimalloc, with only the patched type checker and expression constructor
objects rebuilt from the validated READY trees.

Set `KERNEL_ROOT` to the directory holding the build directories and runner
scripts. In a current project checkout, run:

```sh
LEAN_DEFEQ_ANATOMY=trace LEAN_DEFEQ_MIN_MS=100 \
  lake env bash "$KERNEL_ROOT/current-lean.sh" \
  "$KERNEL_ROOT/build35-release-cpp/bin/lean" <probe>
```

In a historical checkout, run:

```sh
LEAN_DEFEQ_ANATOMY=trace LEAN_DEFEQ_MIN_MS=100 \
  bash "$KERNEL_ROOT/run33.sh" \
  "$KERNEL_ROOT/build33-release-cpp/bin/lean" <probe>
```

Use `counters` in place of `trace` for lower overhead. With the variable
unset the patched binary emits no anatomy report. Both versions retain the
release githash and load the matching project oleans.

`ANATOMY root=` lines contain mutually exclusive comparison and outer-WHNF
times, dependent and proposition comparison/reduction subcategories,
binder-instantiation counts/time, C++ Expr constructor output counts/byte
sizes, and mimalloc process RSS/committed-byte deltas. `ANATOMY branch=`
contains call counts and exclusive comparison/reduction time. Trace mode
also emits the top child calls with parent IDs and inherited component
paths, plus path-prefix totals. A path line's `direct_exclusive_ms` is the
sum at that exact path; `subtree_exclusive_ms` sums direct-exclusive time
over all descendants. Prefix totals overlap their children and must not
be added together. Paths are capped at 160 characters and continue to
aggregate at the capped prefix. `argument[i]` is zero-based; `field[i]`
is the constructor field offset; `binder_domain[i]` and `binder_body[i]`
are positions within a binding comparison. A `proposition_type` path
starts at the proof-irrelevance type check.

The dependent/proposition subcategories are disjoint leaves of the root
comparison/WHNF partition. A nested binder comparison inside a proposition
is assigned to dependent work, so `proposition_*` is not the full span of
all proof-triggered work. The older `proposition_ms` and proof-position
family timers are nested diagnostics and overlap the root partition.
Binder instantiation time also overlaps comparison-exclusive time.

`cpp_expr_created` counts non-scalar outputs of the C++ `mk_*` expression
constructors and `cpp_expr_bytes` sums their object byte sizes. Lean-generated
constructor paths and non-Expr objects are outside this counter; it is not
a process-wide allocation total. RSS/committed-byte deltas are allocator
process snapshots, not retained Expr bytes. The runtime is reference-counted;
no independent GC-time counter is available. The exact-pair capture remains
bounded at five million general recursive calls, and pair keys omit local
context. Raw expression hashes are only grouping proxies.

The READY2 marker files contain the measured fast/slow overhead table and
the exact commands used to validate each binary. The historical case reports
record the separate baseline, counters, and trace measurements. The patches
change observation and output only; comparison results and call counts were
checked against the earlier observational build.
