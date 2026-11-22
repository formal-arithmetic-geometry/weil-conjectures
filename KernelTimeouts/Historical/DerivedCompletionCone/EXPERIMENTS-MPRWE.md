# Mismatch Provenance and Recursive Workload Report

Case: Derived-Completion Cone
Lean / Mathlib: Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
Instrumentation: READY3.1 observational counters, complete aggregates, and bounded trace events.
The target import closure is the historical Complete.Defs closure. The
current-case revision is not used for this historical run.

## 1. Root mismatch

The root is the inferred/declared conversion for `inlineCone` under its
eight-binder dependent telescope. The value is compared with
`Cone (quotPowFunctor J I ⋙ tensorLeft K)`. The established first relevant
representation difference is in the dependent `tensorLeft`/`Functor.comp`
provider structure and its proof fields. The trigger and entry path are
treated as established context, per MPRWE.

READY3 counters reproduced the deterministic kernel timeout with 12,220,823
recursive calls (12,220,746 successful exits and 77 timeout exception exits),
maximum depth 111, 43,167,510 outer WHNF requests, and 187,634 proposition
comparisons. The root span was 103.912 s: 51.518 s comparison-exclusive and
52.393 s outer reduction-exclusive. The detailed trace retained the same call
count and timeout; its root span was 125.914 s, split 68.010 s comparison and
57.904 s reduction. A fresh READY3.1 diagnostic trace completed its selected
1,036-call root in 1.80 s; this is a current-olean diagnostic rather than the
historical 12.221M-call timeout root.

## 2. Matched baseline

The strongest available baseline is A3, not A0/A1. The named diagnostic
uses the same operation family but changes the consumer. READY3 counters gave
34 calls and a 0.092 ms largest nontrivial root. The explicit-instance
diagnostic gave 344 calls and 1.661 ms; the matrix diagnostic gave 38 calls
and 0.113 ms. All are non-identity conversions and typecheck successfully.
They do not preserve the original root conversion, consumer, dependent
telescope, or local preceding arguments. They establish that the smaller
matched diagnostics are cheap, not that the complete root is cheap.

The proof-position audit found 36 differing proof positions. Each isolated
position remained below the timer resolution in the audit. They are not
treated as 36 equal-cost root descendants.

## 3. Provenance distribution

READY3.1 adds stable whole-expression and first-divergence hashes, parent
divergence hashes, reduction before/after hashes, and complete aggregate
records. On the fresh diagnostic trace, the analyzer reports:

| Provenance | Recursive calls | Exclusive time | Status |
|---|---:|---:|---|
| M0 | root entry identified | root entry only | established |
| M1 | 485 | 6.388 ms | 76.7% |
| M2 | 83 | 0.964 ms | 11.6% |
| Matched descendants | 591 | 0.857 ms | 10.3% |
| Unclassified | 2 | 0.066 ms | 0.8% |

The diagnostic had 1,020 entered calls and 1,004 exits for the selected root,
with 293 reductions. Aggregate coverage was 1,020/1,162 calls (87.8%) and
7.841/8.323 ms of exclusive time (94.2%); aggregate path groups retain the
complete totals for the root while raw events are capped.

## 4. Newly exposed divergences

The reduction records now identify the immediately preceding phase and both
heads before and after exposure. Reviewed examples include
`CategoryTheory.MonoidalCategoryStruct.proj -> CategoryTheory.Functor.obj`
inside a dependent category, `CategoryTheory.Functor.proj ->
CategoryTheory.Functor.mk`, and algebraic projection pairs such as
`HAdd.proj -> Add.add`. The hash/path rule identifies 83 M2 calls in the
diagnostic; the top M2 nodes are proof and provider exposures, with 0.964 ms
exclusive time.

## 5. Selective descendant alignment

The chosen M2 was the first proof/provider exposure in the `root/fn/fn/...`
branch. An attempted C1 control aligned that local proof field while keeping
the inline consumer and root telescope; it failed elaboration because the
field is dependent on the original provider, so the intervention is
type-invalid and does not remove M0. The restoration control R restores the
original field and reproduces the original diagnostic result. Existing named,
explicit-instance, matrix, and local-provider controls remain invalid whole
root alignments. No causal speedup is claimed for C1.

## 6. Conclusion

The historical Cone remains a mixed deep comparison/reduction workload. The
fresh READY3.1 diagnostic is primarily M1 (76.7%), with measurable M2 (11.6%)
and matched work (10.3%); Unclassified is 0.8%, well below 50%. The C
intervention is unavailable for the dependent proof field, and R is a
type-preserving restoration of the original mismatch.

## MPRWE round 3 (READY3.2)

The Cone diagnostic is re-read with the READY3.2 root identity. Its M1 76.7%,
M2 11.6%, Matched 10.3%, and Unclassified 0.8% shares are unchanged.

## MPRWE round 4 (READY3.2; current)

The round-3 figures above are superseded. This section is the only current
Cone result. The run used the clean Lean 4.33.1 release worktree with the
READY3.2 patch (process-wide atomic root serial and thread-local active-root
pinning), the historical 4.33.1 import closure, and the READY3.2 analyzer.

### 1. Root and consistency check

The original `OriginalRoot.lean` probe was run with `timeout 3600` and one
Lean thread. The counters run selected root **1847**: **12,220,823** calls,
**82.321 s** comparison-exclusive time, and **163.549 s** instrumented root
span; it ended in the deterministic kernel timeout (12,220,746 successful
exits and 77 timeout exits). The fresh trace selected the same root and call
total, with **84.401 s** comparison-exclusive time and **147.133 s** root
span. The 2.5% comparison-time increase is trace bookkeeping overhead; root
identity and every workload counter match. The trace aggregate is therefore
used for the shares below, with the counters run retained as the consistency
control.

Aggregate coverage is complete: 12,220,823/12,220,823 calls and
84.401/84.401 s exclusive time. Raw capture contains 4,000 bounded events,
1,562 entered calls and 1,496 exits (0.0128% and 0.0122% of root calls); raw
events are for node review only. Analyzer revision: **READY3.2**.

### 2. Provenance distribution (trace aggregate)

| Provenance | Calls | Exclusive time | Time share |
|---|---:|---:|---:|
| M0 | 1 | 0.000059 s | 0.00007% |
| M1 | 9,356,263 | 84.169455 s | 99.72534% |
| M2 | 9,087 | 0.054136 s | 0.06414% |
| Matched | 2,855,469 | 0.177504 s | 0.21031% |
| Unclassified | 3 | 0.000116 s | 0.00014% |

M1 is inherited work in the deep
`root/binder_body[8]/argument[4]/argument[7]/argument[4]/binder_body[1]`
branch. M2 is small by exclusive time; matched descendants are also small
despite 2.86M calls.

### 3. Top captured nodes and reduction review

The bounded raw review found these top five nodes per non-empty label (heads
and first-divergence paths are from the raw event records; times are direct
exclusive time):

* **M1:** `LinearMap.proj` (depth 69, 0.094 ms, `root/expr/fn/fn/arg/...`),
  `LinearMap.comp` (depth 58, 0.091 ms, `root/fn/fn/fn/...`),
  `LinearMap.proj` (depth 74, 0.087 ms, same expression path),
  `LinearMap.mk` (depth 59, 0.087 ms, `root/fn/fn/fn/...`), and
  `LinearMap.proj` (depth 75, 0.087 ms, same expression path). These are
  carried structural divergences (M1), not new reductions.
* **M2:** `CategoryTheory.IsGrothendieckAbelian`/same head (depth 4,
  0.048 ms, proposition path), `Eq`/`Eq` (depth 25, 0.022 ms),
  `inlineCone._proof_2` versus
  `GrothendieckTopology.isGrothendieckAbelian_sheaf_of_essentiallySmall`
  (depth 3, 0.017 ms), `HomologicalComplex.d`/same head (depth 31,
  0.017 ms), and `HomologicalComplex.X`/same head (depth 32, 0.016 ms).
  These are the highest captured M2 nodes; the preceding exposing
  reductions include `Functor.proj -> Functor.mk`,
  `MonoidalCategoryStruct.proj -> Functor.obj`, `HAdd.proj -> Add.add`,
  and `Add.proj -> LinearMap.mk` on the corresponding dependent paths.
* **Matched:** `Category.opposite`/same head (depth 53, 0.012 ms),
  `FullSubcategory.category`/same head (depth 17, 0.008 ms),
  `ModuleCat.Hom.mk`/same head (depth 57, 0.007 ms), `Functor`/same head
  (depth 27, 0.005 ms), and `ModuleCat.Hom.mk`/same head (depth 57,
  0.005 ms). Entry hashes were equal for these descendants.
* **Unclassified:** `DerivedCategory`/same head (depth 1, 0.028 ms);
  no semantic provenance was forced for this retained uncertain node.

### 4. Selective descendant alignment and restoration

The selected top-cost M2 route is the dependent proof/provider exposure in
the `tensorLeft` object branch. `InvalidDescendantAlignment.lean` still
cannot align that field while retaining the original `inlineCone` consumer,
eight-binder telescope, and root M0: the proof field type depends on the
original provider, so replacing it changes the field type and is not a
type-correct descendant-only intervention. `InvalidRootAlignment.lean` and
`InvalidCombinedAlignment.lean` likewise alter the root provider/consumer and
are invalid C controls. The original probe is the restoration R; its fresh
READY3.2 counters reproduce the root and call total above. No causal speedup
or C label change is claimed.

### 5. Conclusion

The Cone is overwhelmingly inherited M1 work by exclusive time (99.725%),
with a small M2 component (0.064%) and a measurable but non-dominant matched
component (0.210%). The dependent proof/provider obstruction prevents a valid
selective descendant alignment; outcome **D** (mixed workload, M1-dominant)
is retained, with the C result reported as unavailable/type-invalid.
