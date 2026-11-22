# Mismatch Provenance and Recursive Workload Report

Case: Derived-Completion Cone
Lean / Mathlib: Lean 4.33.1 `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
Instrumentation: READY3 observational counters and bounded trace events.
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
57.904 s reduction. These are separate counter and trace measurements.

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

The READY3 event stream contains parent/child IDs, paths/categories,
before/after reduction heads, orthogonal tags, and a bounded structural
context fingerprint. The selected trace file is capped and therefore does not
contain complete exit records for all 12.2 million calls. The full root
distribution is consequently retained as Unclassified rather than guessed:

| Provenance | Recursive calls | Exclusive time | Status |
|---|---:|---:|---|
| M0 | root entry identified | root entry only | established |
| M1 | unavailable | unavailable | requires semantic pair review |
| M2 | unavailable | unavailable | reduction candidates captured, no complete attribution |
| Matched descendants | unavailable | unavailable | head equality alone is insufficient |
| Unclassified | 12,220,823 | 51.518 s comparison-exclusive | measured remainder |

The trace sample contains 5,188 enter, 5,113 exit, and 1,874 reduction
events across process-local roots before the event cap. It records dependent
and proposition categories and projection/proof-position tags, but the sample
cap prevents summing them into the root cost. The offline analyzer therefore
reports these as candidates only.

## 4. Newly exposed divergences

The reduction records now identify the immediately preceding phase and both
heads before and after exposure. Reviewed examples include
`CategoryTheory.MonoidalCategoryStruct.proj -> CategoryTheory.Functor.obj`
inside a dependent category, `CategoryTheory.Functor.proj ->
CategoryTheory.Functor.mk`, and algebraic projection pairs such as
`HAdd.proj -> Add.add`. These are exposure events, not automatic M2 labels:
the event stream does not prove that the new head is a distinct relevant
representation boundary. No M2 descendant fan-out or exclusive cost is
claimed from these bounded samples.

## 5. Selective descendant alignment

The required O1/O2/O12/O-all interventions were unavailable. The existing
named, explicit-instance, matrix, and local-provider controls all change the
consumer, provider, or dependent telescope and remove the original root
mismatch. They are copied under `probes/mprwe/` and marked invalid controls.
The original inline source is copied as O and R snapshots. Because no valid
selective descendant intervention preserves M0, no causal M2 savings or
restoration claim is made.

## 6. Conclusion

Outcome E applies to this case. The root is a mixed deep comparison/reduction
workload concentrated in dependent `tensorLeft` and generated proposition
comparisons. The A3 diagnostics and whole-consumer controls show that changing
the outer representation removes the slow root, but they do not distinguish
intrinsically expensive matched descendants from inherited M1 propagation or
new M2 cascades. READY3 supplies the required raw event fields for a future
selected-root audit; the bounded run here leaves 100% of the full-root
provenance attribution Unclassified.
