# Intrinsic vs mismatch-induced DefEq report

Case: PR2122-DiagonalTraceFiniteEtaleIntegralBoundary
Operation family: dependent proposition/body under Exists.casesOn
Revision: current-case oleans at a2ec460045b; READY2 reference profile.
Root conversion: original recursor motive/witness/body context.

OriginalRecursor and RestoredRecursor are O/R; AlignedRecursor is A. M is invalid:
extracting the final branch changes the Exists.casesOn motive and is not the same
root obligation. The fresh O attempt failed before elaboration because the
read-only current tree lacks GmRelativeKummer.olean, so no new Kernel number is
claimed.

Historical READY2 O root: 25,836 ms, 2,227,198 calls, depth 93,
11,486/14,349 ms comparison/reduction, 60,324 Pi-domain and 34,383 proposition
comparisons. Trace: 32,456 ms; 1,535,674 distinct and 691,524 repeated pairs,
287 ms repeat-exclusive. The broad aligned source was 5.142 s / 510,125 calls,
but changes module construction.

Conclusion: H1/H3, limited by the missing olean and recursor validity. No strict
matched control or fresh current-case replay is available; unif_hint is not applicable.

## IM round 2

The original probe still cannot load the required import closure, so no fresh
O/A/R root is claimed. `probes/im/MatchedGeneric.lean` records a diagnostic
same-family proof body at `Exists.casesOn`, compared with an `id`-wrapped
version. The heads are `Exists.casesOn/id`, non-structural, and both sides
kernel-check.

Fresh READY2 zero-threshold counters measured M at `0.038 ms`, two calls, depth
`1`, `0.037/0.001 ms` comparison/reduction, one proposition comparison, and
one `Exists.casesOn|id` proof-position entry; the source check reports `0 ms`.
This is diagnostic only because the original motive/witness/body context is
unavailable without the missing olean.

Verdict: the isolated matched recursor body is cheap; the original case remains
inconclusive for H1/H2/H3, limited by the missing closure. Historical O/A are
AD-phase/reference evidence.
