# PR #1625: TensorSheaf component proof

This pair isolates the historical form of `leftDerivedUpperStarTensorComparison_app_app_fac`, the second of two proofs changed by PR #1625. Both probes use the current prefix and stop immediately after that declaration. The earlier `isLeftDerivedFunctor_leftDerivedUpperStarTensorRight` remains in its fixed form in both. The old closing term needed `maxHeartbeats=10000000` to pass a `whnf` heartbeat limit on Lean 4.35.0; both timed probes use that option.

Both compile under the original module name and generated Lake setup at master revision `1ef1fddac73e`, with Lean 4.35.0, one thread, synchronous elaboration, `nice -n 10`, and profiler threshold 50 ms.

| Probe | Wall s | User CPU s | System CPU s | Peak RSS KB | Target Kernel check |
|---|---:|---:|---:|---:|---:|
| [Before.lean](Before.lean) | 189.31 | 188.18 | 1.30 | 8,245,292 | 87.6 s |
| [After.lean](After.lean) | 104.95 | 104.15 | 1.00 | 2,929,672 | 2.43 s |

An earlier unchanged declaration checks in about 15.4 seconds in both probes; the target accounts for the large difference. The historical PR's full-module measurement was 7.41 to 2.28 GB anonymous memory and 234 to 90 seconds wall with three threads. These cut-prefix results use a different revision and one thread, and isolate only the component proof.

Command form from the master build tree, after placing either probe at its original relative module path under a scratch root:

```sh
LEAN_NUM_THREADS=1 timeout 1200 nice -n 10 /usr/bin/time -v lake env lean \
  -R <scratch-root> <scratch-root>/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/TensorSheaf.lean \
  --setup .lake/build/ir/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/TensorSheaf.setup.json \
  -DElab.async=false -DmaxHeartbeats=10000000 -Dprofiler=true -Dprofiler.threshold=50
```
