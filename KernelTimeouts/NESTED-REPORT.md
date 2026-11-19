# Nested data representation experiments: assigned cases

Scope: the seven `KernelTimeouts/` cases assigned to the nested-data phase,
in Batch 1, Batch 2, and Batch 4 order. The source plan is `NESTED.md`.
All retained measurements use Lean/Mathlib 4.35.0, one Lean thread,
ordinary Kernel checking except explicitly marked phase diagnostics, and
`timeout 3600` with `/usr/bin/time -v`. The fresh matched-control
measurements are summarized in [NESTED-FOLLOWUP.md](NESTED-FOLLOWUP.md);
the earlier exact-site baselines remain linked from each case record.
Kernel-only times and heartbeat counts were not available.

## Observations

| Batch | Case | Retained exact-site A/control result | B/C result | D first producer | Section-12 level |
|---|---|---|---|---|---|
| 1 | [OrderedSpectralRawLattices](OrderedSpectralRawLattices/NESTED-EXPERIMENTS.md) | 200k-heartbeat timeout at 40.23 s; aligned control 10.08 s, checked | B/C harness invalid for imported stored terms | local instance synthesis versus imported theorem type | below 1 strict |
| 2 | [FiniteBaseChangeRestrictionMateTransport](FiniteBaseChangeRestrictionMateTransport/NESTED-EXPERIMENTS.md) | 400k-heartbeat `hb` timeout at 89.36 s; transport control 4.38 s, checked | B harness invalid without rebuilding dependent binder | concrete ProEt site versus mode-indexed helper site | below 1 strict |
| 2 | [EtaleHomComparisonReversedExact](EtaleHomComparisonReversedExact/NESTED-EXPERIMENTS.md) | `hv` application 28.92 s; transport control 3.37 s, checked | B harness invalid without changing quantified consumer | concrete predicate/wrapper versus expanded generic binder | below 1 strict |
| 2 | [F66Adj](F66Adj/NESTED-EXPERIMENTS.md) | argument-39 application 34.72 s; restriction control 3.49 s, checked | B harness invalid without changing accessor head | over-object accessor versus helper's local scheme | below 1 strict |
| 4 | [ImageHomCounit](ImageHomCounit/NESTED-EXPERIMENTS.md) | final `exact` 54.94 s; uniform aligned control 2.59 s, checked | not assigned | imported raw result versus concrete wrapper goal | Level 1 for full alignment |
| 4 | [IntegralComparisonPullbackRealizationShifts](IntegralComparisonPullbackRealizationShifts/NESTED-EXPERIMENTS.md) | original `change` 83.65 s; aligned run 84.14 s, checked site diagnostic | not assigned | tower instance versus operations-comm instance | below 1 for instance cause |
| 4 | [RealPurity](RealPurity/NESTED-EXPERIMENTS.md) | `exact h` timeout at 58.24 s; aligned rings timeout 58.79 s | not assigned | field ring path versus algebraic-closure ring path, then object path | below 1 for ring cause |

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
fanout curve: the attempted wrappers cannot feed imported stored terms
without changing the cost site. No checked four-quadrant A/A, B/B, A/B, B/A
provider matrix was obtained. The A probes provide partial explicit
replays for generic helper arguments, but not a complete instance-term
replay for every case. Therefore Level 2, depth by fanout interactions,
case coverage, and Kernel-cost coverage for a common mechanism cannot be
claimed.

## Measurement boundary

The shared production machine had unrelated Lean workers; this work started
at most four benchmark processes concurrently. The linked fixtures in
`probes/nd/` preserve the exact contexts. Fresh control timings and the
validity outcome for the assigned B/C designs are in `NESTED-FOLLOWUP.md`.
No `sorry`, axiom, or skipped-Kernel diagnostic is counted as a successful
Kernel result.
