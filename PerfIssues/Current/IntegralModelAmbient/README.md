# IntegralModelAmbient: baseline blocked

The eighth ranked module has a handover estimate of 446 whole-module CPU seconds. Re-elaboration of its unchanged source in the master build tree (revision `1ef1fddac73e`, Lean 4.35.0, one Lean thread, synchronous elaboration) exits 1 after 14.98 s wall, 14.07 s user CPU, 0.94 s system CPU, and 3,045,296 KB peak RSS.

The first error, at line 41 of `IntegralModelAmbient.lean`, is a missing `∀ X₁ X₂ X₃ X₄, X₁.HasTensor₄ObjExt X₂ X₃ X₄` instance. The same synthesis failure occurs at lines 70, 76, 95, and 125. Profiler totals are 11.2 s typeclass inference and 0.206 s type checking; the remaining declarations cannot be validly measured after these errors.

Command from the master build tree:

```sh
LEAN_NUM_THREADS=1 timeout 3600 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 \
  WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/IntegralModelAmbient.lean
```

This is an exclusion, not a severe-case classification. A coherent source/import pair or restored graded-tensor instance is needed before profiling its intended declarations.
