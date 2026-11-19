# PR #1627: Weil sheaf transport

These probes stop after `AlgebraicGeometry.ProEtaleWeilSheaf.powFunctor`. [Before.lean](Before.lean) restores its old hand-built functor value on the current prefix; [After.lean](After.lean) applies the generic `IsoAlgebra.liftOfStr` helper. Both compile on Lean 4.35.0, master revision `1ef1fddac73e`, under the original module name and generated Lake setup. Runs used one Lean thread, synchronous elaboration, `nice -n 10`, and `maxHeartbeats=10000000` so the historical value could finish metavariable synthesis.

| Probe | Wall s | User CPU s | System CPU s | Peak RSS KB | Kernel checks introduced by `powFunctor` |
|---|---:|---:|---:|---:|---|
| Before | 109.17 | 107.63 | 1.67 | 7,781,816 | 27.8, 55.3, 14.6 s |
| After | 9.85 | 9.38 | 0.59 | 1,837,544 | none above 50 ms |

The before source with default heartbeats stops at `synthesize pending MVars`; this is a resource-limit failure, so the measured before/after pair uses the same raised limit. The original PR's full-module measurement was 5.53 to 1.65 GB anonymous memory and 264 to 32 seconds wall with three threads. Our cut-prefix numbers are separate 4.35.0 measurements.

Command form from the master build tree, after placing either probe at its original relative module path under a scratch root:

```sh
LEAN_NUM_THREADS=1 timeout 1200 nice -n 10 /usr/bin/time -v lake env lean \
  -R <scratch-root> <scratch-root>/WeilConjectures/WeilSheaf/BaseChangeField/Transport.lean \
  --setup .lake/build/ir/WeilConjectures/WeilSheaf/BaseChangeField/Transport.setup.json \
  -DElab.async=false -DmaxHeartbeats=10000000 -Dprofiler=true -Dprofiler.threshold=50
```
