# Mismatch Provenance and Recursive Workload Report

Case: PR1563-RawModuleScalarPullback
Lean / mathlib: Lean 4.35.0, source snapshot 1ef1fddac73; earlier IM/AD
measurements with READY2-4.35.0.
Root: seven-argument `CategoryStruct.comp` in the dependent `Eq.mpr` domain.

## 1. Root mismatch

The root heads are `CategoryStruct.comp`. The established divergence is in the
`Functor.map`/provider argument (argument 5), with nested composition at the
following argument. Exact expressions and context fingerprints were not in
READY2.

## 2. Matched baseline

The first same-head diagnostic (`MatchedDiagnostic`) is **A3 only**: it keeps
the consumer and root head but changes a provider construction in argument 5.
It type-checks and is non-structural; direct M was 1 ms (earlier IM). It is not
a strict matched root because the dependent morphism type changes. The earlier
full O root was 28,755 ms in the IM round-2 direct check.

## 3. Provenance distribution

Earlier O trace root: 2,573,989 calls, 15,785.269 ms comparison-exclusive,
12,913.573 ms reduction-exclusive, depth 95; 1,723,710 distinct and 850,279
repeated pairs. No parent-child IDs or reduction event records exist.

| Provenance | Calls | Exclusive comparison | Share |
|---|---:|---:|---:|
| M0 | 1 root entry (inferred) | not separable | 0% attributable |
| M1 | not classifiable | not classifiable | Unclassified |
| M2 | not classifiable | not classifiable | Unclassified |
| Matched descendants | not classifiable | not classifiable | Unclassified |
| Unclassified | 2,573,988 recursive calls (inferred) | 15,785.269 ms measured total | 100% of attributable trace |

## 4. Newly exposed divergences

`Functor.obj`, `Functor.map`, nested `CategoryStruct.comp`, and `DFunLike.coe`
are known descendant heads. Their distinct provenance cannot be established
from repeated expression pairs without context, so no M2 fan-out is asserted.

## 5. Selective descendant alignment

| Variant | Result |
|---|---|
| O | Earlier root: 28,755 ms direct; 2,573,989 calls in READY2 counters. |
| O1/O2/O12/O-all | No valid child-only control. Existing A changes argument 5 and hence removes M0; the exact dependent root is different. |
| R | No separate restored timing was available. The earlier aligned control retains a 20.699 s / 1,728,196-call residual root; it is not a selective C intervention. |

## 6. Conclusion

The diagnostic M is cheap and O remains expensive, supporting mismatch-induced
work. The residual aligned root shows a large intrinsic/context floor. Outcome
**D/E**: mixed evidence with all recursive provenance Unclassified. The restored
source snapshot retains the original declaration context; no separate R timing
is claimed.

## MPRWE round 2

READY3.1-4.35.0 fresh counter and trace runs completed. The selected original
root had 2,573,989 calls, depth 95, and 17,289.421 ms aggregate
comparison-exclusive time. Aggregate records are complete; the raw cap was
spent on earlier roots.

| Provenance | Calls | Exclusive ms | Share |
|---|---:|---:|---:|
| M0 | 1 | 0.017 | 0.000% |
| M1 | 1,954,860 | 17,243 | 99.733% |
| M2 | 687 | 4.341 | 0.025% |
| Matched | 618,436 | 41.688 | 0.241% |
| Unclassified | 5 | 0.108 | 0.001% |

The residual root is overwhelmingly M1. The reviewed M2 paths are nested
composition/provider arguments (the largest is argument 5 under the second
composition); they are tiny compared with inherited work. Matched groups in
the same paths total only 0.241%, so the earlier 20.699 s aligned residual is
not evidence of a large M2 cascade.

The provider replacement in the existing aligned probe changes the dependent
root and removes M0, so it is invalid for C. No child-only M2 alignment
type-checks under the original telescope. O and R snapshots are byte-identical;
the earlier aligned residual was 20.699 s. Outcome: **C**.
