# MPRWE Cross-case Synthesis (Round 3)

Analyzer revision: READY3.2. It uses a process-wide atomic root serial in both
instrumented kernels and a root selector that prefers roots with actual raw
coverage. All shares below are from the READY3.1 aggregate records under this
revision; the NativePullTensor validation partition is rejected because its
thread-local root ID mixed worker roots.

| Case | Root calls / exclusive ms | M1 | M2 | Matched | Unclassified | C result | Outcome |
|---|---:|---:|---:|---:|---:|---:|---|
| Derived-Completion Cone | 1,162 / 8.323 | 76.7% | 11.6% | 10.3% | 0.8% | dependent-field restoration | D |
| FiniteBaseChange | 239,340,712 / 880,519.949 | 74.441% | 23.947% | 1.614% | 0.000% | descendant alignment restored | D |
| IntegralComparison | 9,426,253 / 43,830.207 | 98.400% | 1.328% | 0.255% | 0.017% | first-leaf alignment restored | C |
| RealPurity | 17,310,168 / 76,192.584 | 62.046% | 36.568% | 1.389% | 0.000% | restoration setup repaired | D |
| OrderedSpectralRawLattices | 18,944,709 / 58,992.669 | 63.902% | 35.347% | 0.758% | 0.000% | restoration setup repaired | D |
| EtaleHom | 3,180,470 / 21,549.825 | 99.762% | 0.001% | 0.236% | 0.001% | no valid descendant-only control | C |
| F66Adj | 3,897,905 / 24,659.468 | 99.743% | 0.000% | 0.257% | 0.000% | no valid descendant-only control | C |
| ImageHomCounit | 6,359,958 / 42,708.813 | 99.761% | 0.007% | 0.232% | 0.000% | no valid descendant-only control | C |
| RealPushforward | 17,340,236 / 75,988.013 | 61.473% | 37.204% | 1.326% | 0.000% | no valid descendant-only control | D |
| NativePullTensor | 2,685,580 / 20,675.658 | 98.124% | 0.299% | 1.581% | 0.000% | root provider alignment invalid | C |
| PR1556 | 6,670,198 / 45,113.186 | 99.700% | 0.072% | 0.228% | 0.000% | major-premise alignment invalid | C |
| PR1625 | 11,757,788 / 68,508.492 | 99.471% | 0.071% | 0.456% | 0.001% | outer-major alignment invalid | C |
| PR1563 | 2,573,989 / 17,289.421 | 99.733% | 0.025% | 0.241% | 0.001% | provider alignment invalid | C |
| PR1624 | 6,598,545 / 40,848.850 | 99.809% | 0.006% | 0.185% | 0.001% | endpoint alignment invalid | C |
| PR1627 | 10,904,899 / 28,458.907 | 66.352% | 24.928% | 8.727% | 0.000% | generated-field descendant restored | D |
| PR2122 | 2,227,198 / 13,821.715 | 98.901% | 0.876% | 0.201% | 0.021% | recursor alignment invalid | C |

## §11 Answer

The workload is mixed. Inherited M1 propagation dominates every M1-classified
root, while FiniteBaseChange, RealPurity, OrderedSpectralRawLattices,
RealPushforward, and PR1627 have material newly exposed M2 shares. Matched
descendants are measurable but never cost-dominant. The selective descendant
experiment is valid for FiniteBaseChange, IntegralComparison, and PR1627; the
remaining attempted alignments change the root telescope or remove M0 and are
reported as invalid. The NativePullTensor contradiction was an event-stream
root-ID collision, resolved by the READY3.2 atomic root identity.
