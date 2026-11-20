# PerfIssues Targeted Follow-up Experiments

Lean 4.35.0, snapshot `1ef1fddac73`, instrumentation build READY-4.35.0.
The reports use the existing in-situ and replay probes and add the A2/C
validity decisions required by `AD.md`. All numeric values below are measured;
interpretations are labelled as such. No READY2 build was present during this
batch, so no component-path or allocation rerun was available.

| Case | Experiments | Measured result | Outcome |
|---|---|---|---|
| NativePullTensor | A1, A2 | 2.686M calls; depth 81; 22.333 s comparison + 11.746 s reduction. `Functor.obj`/major-premise A/A 0 ms versus A/B 11,396 ms and reverse 11,284 ms. | A causal accessor-premise component; remaining cost is distributed. B/C invalid. |
| PR1556 | A1, A2 | 6.670M calls; depth 213; 39.404 s comparison + 37.784 s reduction. `NatTrans.app` A/B 50,090 ms, A/A 0, reverse 50,585 ms. | A causal major-premise component; deep mixed tree remains. B/C invalid. |
| PR1625 | A1, A2 | 11.758M calls; depth 125; 70.713 s comparison + 57.127 s reduction. Nested app A/B 95,869 ms, A/A 0, reverse 93,567 ms. | A causal nested app premise; outer and inner sites share the mechanism. B/C invalid. |
| PR1563 | A1, partial A2 | 2.574M calls; depth 95; 16.070 s comparison + 17.154 s reduction. Seven arguments range from 0 to 22.374 s; nested composition is largest. | Distributed mixed cost; no reversible single-component A2. B/C not validly isolated. |
| PR1627 | A1, B attempt, C | 10.905M calls; depth 61; 20.611 s comparison + 20.198 s reduction. Generated fields 27.8/55.3/14.6 s; id domains 7.608/32.992 s. | Repeated generated dependent fields and proposition applications; B/A2 invalid. C confirms shared shape, not equal cost. |
| PR1624 | A1, C | 6.599M calls; depth 88; 38.767 s comparison + 37.985 s reduction. Full endpoints 14.769/29.112 s while isolated args are 0--8 ms; aligned root 5.256 s/456k calls. | Full dependent endpoint creates the work; neither component A2 nor B preserves the telescope. |
| PR2122 | C in original recursor | 2.227M calls; depth 93; 11.486 s comparison + 14.349 s reduction. Motive 16.115 s and witness 18.419 s; final branch cannot be checked alone. | Branch-local dependent work is measured; component and provider attribution remains unresolved. |

## Cross-case conclusions

1. The causal A2 controls that type-check (NativePullTensor, PR1556, PR1625)
   remove the same measured representation-premise cost and restore it in the
   reverse direction. This is evidence for a concrete component contribution,
   not merely a high unfold count.
2. The selected current roots are mixed. Comparison and reduction are both
   material; selected roots do not support a reduction-only explanation.
3. Exact pair repetition is visible, but its measured exclusive share is small
   in the selected roots (about 0.5--11.2%). Pair keys omit local-context
   identity, so this is a bounded repetition result rather than a cache claim.
4. Dependent endpoints can be expensive even when their individual arguments
   are cheap (`PR1624`). The trace records many Pi-domain and proposition
   comparisons, but proposition timers are nested and cannot be added to the
   exclusive comparison/reduction totals.
5. PR1627 provides repeated generated-field evidence: two fields use the same
   dependent `id`-proposition shape, while their costs differ substantially.
   The generic helper is a construction control, not a shared-provider
   experiment.
6. PR2122's final dependent branch is ill-typed outside its `Exists.casesOn`
   motive. The measured motive and witness checks are retained, and no cost is
   attributed to the uncheckable branch.

Allocation/GC counters were unavailable in READY-4.35.0; RSS changes are not
reported as allocation. The validated instrumentation overhead was 1.32 s
release, 1.48 s counters, 1.42 s trace on the fast control, and 49.39/53.79/
59.81 s on the slow NativePullTensor control.

Per-case records and compact measured probe summaries are in each case's
`EXPERIMENTS-AD.md` and `probes/ad/profile.txt`.
