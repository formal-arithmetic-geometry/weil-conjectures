# IntegralModelAmbient

The eighth ranked module has a handover estimate of 446 whole-module CPU seconds. The renamed-copy run was invalid. Replaying the unchanged source under its original module name with the generated lake setup succeeds: 186.9 s wall, 191.41 s user CPU, 0.79 s system CPU, and 2,576,920 KB peak RSS. The profiler reports one 159 s `refine`, with 5.75 s type checking and 22.4 s typeclass inference.

The successful run reaches `exists_derivedCompleteIntegers_iso_integralModel_aux` and its public wrapper. The old error at line 41 was caused by compiling under a different module name and must not be used as a performance result.

Command from the master build tree:

```sh
LEAN_NUM_THREADS=1 timeout 3600 nice -n 10 /usr/bin/time -v lake env lean \
  WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/IntegralModelAmbient.lean \
  --setup .lake/build/ir/WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/IntegralModelAmbient.setup.json \
  -Dprofiler=true -Dprofiler.threshold=50000
```

This is an elaboration-heavy valid case. The exact Meta operation inside the 159 s `refine` remains open; no A–F Kernel label is assigned.
