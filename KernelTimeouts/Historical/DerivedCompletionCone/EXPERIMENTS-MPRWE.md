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
