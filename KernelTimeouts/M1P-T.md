# KernelTimeouts M1 propagation: READY4.2

All rows are fresh Lean 4.35.0 runs from the reserved `m1p` import revision
`105ac3f5b23`, using the READY4.2 kernel/analyzer (`0311a15b5f4`). Counter
root calls equal analyzed aggregate calls in every completed case. Aggregate
label, transition, depth, and fan-out values cover the complete selected
root; raw enter/exit coverage is bounded and reported in each case report.

For mixed cases, the table reports the median of three trace runs and the
minimum--maximum time-share spread. Call shares and call counts are
deterministic. Shape is the analyzer rule: deep means median depth >=75,
mean fan-out <=1.5, and 90%-time band width <=32; wide means fan-out p90 >=8
and median depth <75; all remaining cases are mixed.

| Case | Calls | M1 call share | M1 time share | M1 calls | Depth median/p90/max | 50% band | Mean fan-out | Fan-out p90 | M1->M1 / Matched / M2 | Dominant M1 transition | Shape | C |
|---|---:|---:|---:|---:|---|---|---:|---:|---:|---|---|---|
| EtaleHom | 3,180,470 | 75.171% | 99.735% | 2,390,795 | 79/90/111 | 71--83 | 1.330 | 3 | 2,390,783 / 789,627 / 15 | projection -> projection | deep | no M0-preserving `hv` cut |
| FiniteBaseChange | 239,340,712 | 54.398% | 72.869% [72.843--73.112%] | 130,197,227 | 75/79/87 | 71--74 | 1.081 | 1 | 89,755,076 / 23,447,508 / 27,479,827 | projection -> projection | deep | step-2 no-effect / no valid new cut |
| RealPurity | 17,310,168 | 46.148% | 62.315% [62.170--64.097%] | 7,988,264 | 86/88/91 | 84--86 | 1.274 | 1 | 6,491,456 / 1,695,794 / 1,987,467 | projection -> projection | deep | not requested |
| OrderedSpectralRawLattices | 18,944,709 | 43.922% | 64.684% [62.351--64.750%] | 8,320,909 | 64/68/71 | 60--65 | 1.754 | 8 | 5,076,832 / 6,741,771 / 2,780,258 | application -> argument | wide | not requested |
| RealPushforward | 17,340,236 | 46.148% | 61.446% [61.312--63.086%] | 8,002,209 | 84/86/89 | 82--84 | 1.274 | 1 | 6,502,766 / 1,698,481 / 1,990,961 | projection -> projection | deep | not requested |
| IntegralComparison | 9,426,198 | 70.875% | 99.551% | 6,680,842 | 109/133/181 | 97--116 | 1.406 | 3 | 6,672,675 / 2,702,845 / 20,527 | projection -> projection | mixed | not requested |
| F66Adj | 3,897,905 | 75.968% | 99.803% | 2,961,163 | 90/102/121 | 85--98 | 1.316 | 3 | 2,961,160 / 936,731 / 9 | projection -> projection | mixed | not requested |
| ImageHomCounit | 6,359,958 | 75.178% | 99.768% | 4,781,271 | 162/173/204 | 155--167 | 1.330 | 3 | 4,781,165 / 1,578,192 / 157 | projection -> projection | deep | not requested |

The new M1-parent matrices make projection descent the dominant M1 strategy
in EtaleHom, FiniteBaseChange, RealPurity, RealPushforward, IntegralComparison,
F66Adj, and ImageHomCounit. OrderedSpectralRawLattices is the exception:
application-argument descent is its largest M1-only row while M2 remains
34.5% of time. The detailed case reports give the rows covering at least 90%
of M1 exclusive time; mixed roots include non-M1 parents that feed M1
children so that the coverage claim is complete.
