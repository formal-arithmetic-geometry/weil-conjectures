# MPRWE cross-case synthesis

## MPRWE round 4 (READY3.2)

Toolchain: Lean 4.35.0, current-case revision 2e92d5989ff. Analyzer:
READY3.2 mprwe_analyze.py with process-wide atomic root identity and raw
coverage root selection. Values below use only the fresh round-4 roots.
Counter exclusive time is the READY3.2 counters run; aggregate exclusive time
and label shares are from the pinned READY3.2 trace. Trace timing includes
hash/path overhead. Raw coverage is traced calls / total calls.

| Case | Counter O calls / ms | Analyzed root calls / aggregate ms | Raw coverage | M0 | M1 | M2 | Matched | Unclassified | C result | Outcome |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|---|
| FiniteBaseChange | 239,340,712 / 681,687.160 | 239,340,712 / 1,082,179.217 | 3,828 / 239,340,712 | 0.000% | 74.113% | 24.473% | 1.414% | 0.000% | descendant alignment root-changing; restoration diagnostic | D |
| IntegralComparison | 9,426,198 / 83,768.275 | 9,426,198 / 224,445.716 | 3,913 / 9,426,198 | 0.000% | 99.839% | 0.052% | 0.109% | 0.000% | After root-changing; Before restored | C |
| RealPurity | 17,310,168 / 52,925.953 | 17,310,168 / 85,908.939 | 3,222 / 17,310,168 | 0.000% | 63.672% | 35.139% | 1.189% | 0.000% | no M0-preserving type-correct control | D |
| OrderedSpectralRawLattices | 18,944,709 / 35,362.863 | 18,944,709 / 65,054.912 | 4,333 / 18,944,709 | 0.000% | 62.919% | 36.382% | 0.698% | 0.000% | route controls root-changing | D |
| EtaleHom | 3,180,470 / 22,573.922 | 3,180,470 / 26,975.321 | 4,124 / 3,180,470 | 0.001% | 99.800% | 0.002% | 0.197% | 0.000% | hv alignment root-changing | C |
| F66Adj | 3,897,905 / 26,603.785 | 3,897,905 / 30,149.979 | 3,685 / 3,897,905 | 0.000% | 99.791% | 0.000% | 0.209% | 0.000% | hR alignment root-changing | C |
| ImageHomCounit | 6,359,958 / 42,138.453 | 6,359,958 / 42,672.620 | 3,773 / 6,359,958 | 0.001% | 99.761% | 0.009% | 0.230% | 0.000% | endpoint alignment root-changing | C |
| RealPushforward | 17,340,236 / 125,356.436 | 17,340,236 / 105,827.556 | 3,122 / 17,340,236 | 0.000% | 63.011% | 35.985% | 1.003% | 0.000% | polynomial alignment root-changing | D |

The per-case reports contain the required top-five raw nodes per non-empty
label and the M2 reduction event review. Older round-2/3 tables in those
reports are superseded by their round-4 sections.

Outcome: four cases are M1-dominated (IntegralComparison, EtaleHom, F66Adj,
ImageHomCounit); four have material M2 amplification (FiniteBaseChange,
RealPurity, OrderedSpectralRawLattices, RealPushforward). No C control changes
the root while preserving the requested outer dependent telescope. Branch
head before the round-4 commit: a9c7d479cdb.
