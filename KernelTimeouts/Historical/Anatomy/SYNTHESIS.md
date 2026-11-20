# Cross-Case DefEq Cost Anatomy

This table combines the two historical reference roots (Lean 4.33.1)
with seven current KernelTimeouts roots and seven current PerfIssues
roots (Lean 4.35.0). All 16 rows are direct counter-mode measurements
from the case reports; root spans partition into exclusive comparison
and outer-WHNF/reduction time. T's RealPurity and RealPushforward rows
are partial roots stopped by deterministic timeouts. The current-case
reports used an earlier observational patch revision; their measurements
are retained with that revision. P selected one representative root per
case, while some files have additional expensive roots. These totals
therefore describe the selected conversions, not whole modules.

| Case | Root s | WHNF s | Compare s | Calls | Depth | Fan-out evidence | Exact repeats in trace | Allocation |
| --- | ---: | ---: | ---: | ---: | ---: | --- | ---: | --- |
| Slow Derived Tensor | 42.025 | 19.182 | 22.844 | 6,269,622 | 96 | max 28 | 1,666,128 / 5m | unmeasured |
| Derived-Completion Cone | 105.142 | 53.297 | 51.845 | 12,220,822 | 111 | max 28 | 1,583,761 / 5m | unmeasured |
| ImageHomCounit | 73.084 | 35.939 | 37.145 | 6,359,958 | 204 | 1,346,313 multi-child | 1,644,449 / 5m | unmeasured |
| EtaleHomComparisonReversedExact | 36.191 | 17.484 | 18.707 | 3,180,470 | 111 | 673,160 multi-child | 1,046,492 / 3.18m | unmeasured |
| FiniteBaseChangeRestrictionMateTransport | 813.972 | 0.076 | 813.896 | 239,340,712 | 87 | 11,255,747 multi-child | 3,534,109 / 5m | unmeasured |
| F66Adj | 44.174 | 21.373 | 22.801 | 3,897,905 | 121 | 833,071 multi-child | 1,290,616 / 3.90m | unmeasured |
| IntegralComparisonPullbackRealizationShifts | 110.020 | 41.363 | 68.656 | 9,426,253 | 183 | 1,986,478 multi-child | 1,781,432 / 5m | unmeasured |
| RealPurity (partial) | 64.277 | 0.010 | 64.267 | 17,340,901 | 93 | 815,335 multi-child | 3,545,573 / 5m | unmeasured |
| RealPushforward (partial) | 63.942 | 0.004 | 63.938 | 17,340,236 | 91 | 815,279 multi-child | 3,545,728 / 5m | unmeasured |
| NativePullTensor | 34.078 | 11.746 | 22.333 | 2,685,580 | 81 | max 28* | 1,842,979 / 2.69m | unmeasured |
| PR1556 | 77.188 | 37.784 | 39.404 | 6,670,198 | 213 | max 21* | see case trace | unmeasured |
| PR1625 | 127.840 | 57.127 | 70.713 | 11,757,788 | 125 | max 44* | see case trace | unmeasured |
| PR1627 | 40.808 | 20.198 | 20.611 | 10,904,899 | 61 | max 18* | see case trace | unmeasured |
| PR1563 | 33.224 | 17.154 | 16.070 | 2,573,989 | 95 | max 25* | see case trace | unmeasured |
| PR1624 | 76.752 | 37.985 | 38.767 | 6,598,545 | 88 | max 21* | see case trace | unmeasured |
| PR2122 | 25.836 | 14.349 | 11.486 | 2,227,198 | 93 | max 31* | see case trace | unmeasured |

`multi-child` counts come from T's selected roots; `max` means maximum
children in a trace. Asterisked P maxima cover the full trace probe and
are not guaranteed to occur in the selected root. General pair capture
is capped at five million calls. P's case summary provides distinct-pair
counts and repeated-pair exclusive-time shares rather than repeat counts
for every case; those values are in its case reports. The NativePullTensor
repeat count is the independently rerun current domain root on the final
patch, with the same 2,685,580 calls as P's selected root. The historical
trace measured 3,333,872 and 3,416,239 distinct exact general pairs
respectively. Raw structural hashes are grouping proxies, not proofs of
structural equality; the patch does not record local-context identity.

## Cost categories and coverage

Across the 16 selected counter roots, measured root time is 1,768.553 s.
Exclusive comparison accounts for 1,383.483 s (78.2%) and outer WHNF
for 385.072 s (21.8%); 2 ms of difference from root time is display
rounding. The T roots contribute 1,205.660 s of that sample and
FiniteBaseChange alone contributes 813.972 s, so aggregate percentages
are workload-weighted, not typical-case percentages. P's selected
roots contribute 415.726 s; historical roots contribute 147.167 s.

- **Reduction dominated:** none is unambiguously dominated by exclusive
  WHNF time. PR2122 has 14.349/25.836 s (55.5%) and the Cone has
  53.297/105.142 s (50.7%), both mixed. High Delta counts in the
  historical roots are cheap direct unfolds: 0.846 s of 42.025 s for
  Tensor and 2.147 s of 105.142 s for Cone.
- **Comparison dominated:** FiniteBaseChange, RealPurity, and
  RealPushforward have more than 99.9% exclusive comparison time.
  Together they cover 942.191 s (53.3%) of selected root time.
  The latter two are partial timeout roots. The other 13 cases
  cover 826.362 s (46.7%) and have mixed profiles.
- **Dependent/proposition work:** historical Tensor entered 79,290
  proposition comparisons and Cone 187,634. Nested-exclusive
  proposition frames put 41.930/42.025 s and 105.106/105.142 s
  respectively inside generated `Eq` checks; those frames overlap
  comparison and WHNF categories. P's and T's reports also locate
  expensive dependent domains and proof propositions, but no shared
  exclusive dependent-type timer establishes a project-wide share.
- **Depth and fan-out:** seven of 16 selected roots exceed depth 100
  (573.639 s, 32.4% of selected time). PR1556 reaches 213,
  ImageHomCounit 204, and IntegralComparison 183. PR1625's full
  trace probe reaches fan-out 44; the historical roots reach 28.
  FiniteBaseChange has 11.26 million multi-child calls. Both narrow
  deep and broad repeated workloads occur.
- **Repeated work:** all 16 traces found exact repeated general
  expression-node pairs, covering all selected cases. The capped
  capture can substantially understate full-run repeats. In the
  historical roots, 1.67m/5m and 1.58m/5m general pairs repeat, but
  their 79,290 and 187,634 proposition pairs are all exact-distinct.
  Immediate exclusive time in repeated sampled calls is small
  (0.267 s Tensor, 0.444 s Cone); descendant replay cost was not
  measured. P's repeated-pair exclusive shares are 0.5-11.2% of
  trace comparison time. Repetition frequency alone does not prove
  repeated work dominates root time.
- **Allocation and memory:** zero of 16 cases can be classified as
  allocation dominated. RSS was measured, including 23,966,284 kB
  for the FiniteBaseChange release diagnostic, but Expr allocation,
  live bytes, GC time, and phase-specific memory were not instrumented.

The historical pair shares a mixed comparison/reduction signature with
ImageHomCounit, EtaleHom, F66Adj, and most P roots. The Cone and Tensor
traces further identify generated equality proof checks as the
long-running nested spans; that family-level diagnosis is not proven
for the current cases by the shared exclusive partition. FiniteBaseChange
and the two Real timeout roots are a different comparison-heavy shape.
On the directly rebuilt fixed Tensor revision, the full consumer took
3 ms forward and 2 ms reverse while its standalone instance argument
still took 52.535 s; the fix changed which work the parent demanded.
The patch cannot assign a full per-field path, exact repeated-subtree
share, or memory cost to any of these roots. These are explicit limits
of the current measurements, not missing root reproductions.
