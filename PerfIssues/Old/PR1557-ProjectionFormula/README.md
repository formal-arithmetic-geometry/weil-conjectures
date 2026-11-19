# PR #1557: projection formula candidate, not reproduced

Historical PR #1557 removed a braided-category instance and a braiding morphism from two boundedness proofs in `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ProjectionFormula`. The files here port both forms onto the current source prefix under Lean 4.35.0, master build revision `1ef1fddac73e`, single-threaded synchronous elaboration.

| Scope | Historical wall / user CPU s | Fixed wall / user CPU s | Historical / fixed peak RSS KB |
|---|---:|---:|---:|
| First changed lemma, [Before.lean](Before.lean) / [After.lean](After.lean) | 4.19 / 3.27 | 4.01 / 3.09 | 3,160,580 / 3,146,428 |
| Both changed lemmas, [BeforeBoth.lean](probes/BeforeBoth.lean) / [AfterBoth.lean](probes/AfterBoth.lean) | 4.93 / 4.01 | 4.51 / 3.57 | 3,158,552 / 3,144,004 |

All four runs succeeded. Per-declaration type checking for the first lemma was 0.353 s historical versus 0.199 s fixed; across both lemmas, cumulative type checking was 0.694 s historical versus 0.374 s fixed. Thus these isolated proofs do not reproduce the old 10.7-to-4.0 GB whole-module memory reduction on this revision. The historical report may have measured downstream declarations or a different import/instance environment; neither was tested here. No A–F mechanism is assigned to these cheap isolated forms.

Command form, run from the master build tree:

```sh
LEAN_NUM_THREADS=1 timeout 1200 nice -n 10 /usr/bin/time -v lake env lean \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50 SOURCE
```

This candidate was stopped after the changed proof pair passed cheaply. It is excluded from the performance-case table.
