# PR #1624: IntegersSheafHomologyTower

The before probe restores the old value of `AlgebraicGeometry.ProEtale.homologyIntegersTowerIso` in the current module. The after probe uses the current value. The declaration is last in both files. Both compiled successfully on Lean 4.35.0, master revision `1ef1fddac73e`, with one Lean thread, synchronous elaboration, `nice -n 10`, and profiler threshold 50 ms. Each was replayed under the original module name using its generated Lake setup.

| Probe | Wall s | User CPU s | System CPU s | Peak RSS KB | Target Kernel check |
|---|---:|---:|---:|---:|---:|
| [Before.lean](Before.lean) | 112.48 | 111.38 | 1.11 | 11,038,208 | 102 s |
| [After.lean](After.lean) | 12.44 | 11.77 | 0.70 | 2,668,464 | 3.18 s |

The two earlier checks of about 2 seconds each occur in both probes. Tactic execution totals under 1 second in both. The current fixed source introduces `homologyIntegersTowerIsoAux` over abstract functors, plus named comparison isos; the old value assembles the same final iso directly over concrete derived functors. The PR's original 3-thread measurement reported 9.15 GB to 1.08 GB anonymous memory and 89 to 12 seconds wall. Our single-thread results above are separate 4.35.0 measurements.

Command form from the master build tree, after placing either probe at its original relative module path under a scratch root:

```sh
LEAN_NUM_THREADS=1 timeout 1200 nice -n 10 /usr/bin/time -v lake env lean \
  -R <scratch-root> <scratch-root>/WeilConjectures/SixFunctors/ProEtale/Adic/IntegersSheafHomologyTower.lean \
  --setup .lake/build/ir/WeilConjectures/SixFunctors/ProEtale/Adic/IntegersSheafHomologyTower.setup.json \
  -DElab.async=false -Dprofiler=true -Dprofiler.threshold=50
```
