# AffineLineConstant: baseline blocked

The module is ranked third in the handover (708 estimated whole-module CPU seconds), but re-elaboration of the unchanged current source in the master build tree did not produce a valid target declaration. Lean 4.35.0, built revision `1ef1fddac73e`, `LEAN_NUM_THREADS=1`, `nice -n 10`, `-DElab.async=false`, profiler threshold 50 ms: 44.59 s wall, 43.57 s user CPU, 1.05 s system CPU, 3,580,140 KB peak RSS, exit status 1.

The first errors are at source lines 93-96 in `isIso_unit_app_of_isIso_baseChangeMap_app`: missing `∀ X₁ X₂ X₃ X₄, X₁.HasTensor₄ObjExt X₂ X₃ X₄` and `L((𝟙 X)^*⟦Λ⟧).Full`. Later `leftDerivedExtendScalarsTensorUnitIso` at line 115 has the same missing graded-tensor instance and `MonoidalClosed`; line 118 reaches a deterministic typeclass heartbeat timeout. There are 22 errors before the target theorem `isIso_affineLineUnit_app_tensorUnit_padicAlgCl` can be validly measured. Profiler totals on the failing run: 31.9 s typeclass inference, 5.79 s type checking, 3.1 s tactics. These are error-recovery timings, not a whole-module baseline.

Command from the master build tree:

```sh
LEAN_NUM_THREADS=1 timeout 3600 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 \
  WeilConjectures/SixFunctors/ProEtale/ModuleObject/BaseChangeTheorems/AffineLineConstant.lean
```

No measured severe declaration or A–F diagnosis is claimed for this candidate. Repairing the missing instances or obtaining a coherent source/import pair is required first.
