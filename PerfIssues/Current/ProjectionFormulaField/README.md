# ProjectionFormulaField

The ninth handover candidate was previously reported as failed because the source was compiled under a renamed module. Replaying the unchanged source under its original module name and generated lake setup succeeds on Lean 4.35.0: 128.1 s wall, 150.23 s user CPU, 0.81 s system CPU, and 2,685,396 KB peak RSS. The profiler reports 124 s elaboration, 1.94 s type checking, and 918 ms typeclass inference.

The dominant declaration is `projectionFormula_baseChange_localizingBoundedConstructible_continuousMapRingObj` (the field section, around lines 140-153); the same construction is repeated for the algebraically closed coefficient field. This is an elaborator case, not a missing-instance baseline. A bounded `Meta.isDefEq` trace on the shared scalar reproduction was too noisy to isolate a single inner conversion, so the mechanism remains open.

Command from the master build tree:

```sh
LEAN_NUM_THREADS=1 timeout 3600 nice -n 10 /usr/bin/time -v lake env lean -R <same-name-root> \
  WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/ProjectionFormulaField.lean \
  --setup .lake/build/ir/WeilConjectures/SixFunctors/ProEtale/ModuleObject/Derived/ProjectionFormulaField.setup.json \
  -Dprofiler=true -Dprofiler.threshold=50000
```

