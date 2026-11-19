# Nested data representation experiments: assigned cases

Scope: the seven `KernelTimeouts/` cases assigned to the nested-data phase,
in Batch 1, Batch 2, and Batch 4 order. The source plan is `NESTED.md`.
All retained measurements use Lean/Mathlib 4.35.0, one Lean thread,
ordinary Kernel checking except explicitly marked phase diagnostics, and
`timeout 3600` with `/usr/bin/time -v` in the prior workplan sessions,
at the heartbeat setting stated in each case record. Each case record links
its source snapshot, exact consumer, variant, measured result, and
representation provenance. Timings in this report were collected in the
earlier workplan sessions and are reused; there are no new timed runs in
this phase. Kernel-only times and heartbeat counts were not available.

## Observations

| Batch | Case | Retained exact-site A/control result | B/C result | D first producer | Section-12 level |
|---|---|---|---|---|---|
| 1 | [OrderedSpectralRawLattices](OrderedSpectralRawLattices/NESTED-EXPERIMENTS.md) | 200k-heartbeat timeout at 40.23 s; all three instance routes disabled: 10.11 s, checked; partial removals still time out | B/C not measured | local instance synthesis versus imported theorem type | below 1 strict |
| 2 | [FiniteBaseChangeRestrictionMateTransport](FiniteBaseChangeRestrictionMateTransport/NESTED-EXPERIMENTS.md) | 400k-heartbeat `hb` timeout at 89.36 s; exact-proposition transport: 4.40 s, checked application | B not measured | concrete ProEt site versus mode-indexed helper site | below 1 strict |
| 2 | [EtaleHomComparisonReversedExact](EtaleHomComparisonReversedExact/NESTED-EXPERIMENTS.md) | `hv` application 28.92 s; predicate/domain/all-wrapper exposures remain about 29 s; exact-proposition transport: 3.40 s | B not measured | concrete predicate/wrapper versus expanded generic binder | below 1 strict |
| 2 | [F66Adj](F66Adj/NESTED-EXPERIMENTS.md) | argument-39 application 34.72 s; direct restriction proof: 3.40 s; preceding-isomorphism control: 35.12 s | B not measured | over-object accessor versus helper's local scheme | below 1 strict |
| 4 | [ImageHomCounit](ImageHomCounit/NESTED-EXPERIMENTS.md) | final `exact`: 54.94 s; first-wrapper exposure: 83.45 s; fully aligned inferred target with same proof: 2.60 s | not assigned | imported raw result versus concrete wrapper goal | Level 1 for full alignment |
| 4 | [IntegralComparisonPullbackRealizationShifts](IntegralComparisonPullbackRealizationShifts/NESTED-EXPERIMENTS.md) | original `change`: 83.65 s; aligned first instance: 83.15 s; skip-Kernel diagnostic: 4.20 s | not assigned | tower instance versus operations-comm instance | below 1 for instance cause |
| 4 | [RealPurity](RealPurity/NESTED-EXPERIMENTS.md) | `exact h` timeout at 58.24 s; aligning both ring leaves still times out at 58.44 s; alternate polynomial transport: 7.10 s local proof | not assigned | field ring path versus algebraic-closure ring path, then object path | below 1 for ring cause |

Each fast row is a matched *within-case* control retaining much of the
original data and consumer. None is an independent nearby fast declaration
with the same hierarchy, depth, and fanout. Thus the section-9 project
comparison and section-12 Level 3 are not established.

## Interpretation

The retained controls support representation alignment at several exact
Kernel cost sites, especially the full target alignment in ImageHomCounit.
They do not establish the full project-level nested-data hypothesis. The
OrderedSpectral instance bundle must be aligned together; exposing only one
successive wrapper in EtaleHomComparisonReversedExact leaves the cost; and
the first visible instance leaves in IntegralComparison and RealPurity are
not sufficient causes. These results favor a multi-stage representation
account over an explanation based solely on the first structural mismatch.

No case has a valid fixed-leaf depth curve or fixed-depth repeated-field
fanout curve. No checked four-quadrant A/A, B/B, A/B, B/A provider matrix
was obtained, and none of the earlier source probes separates instance
synthesis from an explicit-instance Kernel replay as section 2.2 requires.
The prior Kernel-skip diagnostics distinguish broad elaboration versus
Kernel phases but do not replace that replay. Therefore Level 2, depth by
fanout interactions, case coverage, and Kernel-cost coverage for a common
mechanism cannot be claimed.

## Measurement boundary

The shared production machine already had seven pre-existing Lean
server/worker processes when this phase began, above the task's cap of six
Lean processes at once. Those processes were not started by this work and
were not stopped. No new Lean process was launched. The linked fixtures in
`probes/nd/` preserve the earlier checked controls for later reruns; they
are not presented as newly measured evidence. New A provider matrices,
B/C curves, explicit replays, and independent section-9 fast controls
remain outstanding. No `sorry`, axiom, or skipped-Kernel diagnostic is
counted as a successful Kernel result.
