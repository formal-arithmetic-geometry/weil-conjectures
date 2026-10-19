# NF maintenance: vector-bundle purity prerequisite compatibility

The repeated stage-2 failures of `thm-amb-vector-bundle-purity` were prerequisite
import/interface failures. The theorem's mathematical statement does not need to
be changed to fix these failures.

`FiniteCoefficient.UpperLowerStar.Defs` copied the published pro-etale functors
under their original public names. It now imports the canonical module and keeps
only its additional identity-comparison definition. The source-override manifest
selects this compatibility module even when an older published artifact exists.

K-flat centralization had also broken compiled consumers: the old forwarding
module could still be loaded through a published intermediate importer; three
helper names changed universe arity; and the independent-coefficient predicates
gained instance arguments. Both compilers now prepare explicit replacements
before consumers. The published helper signatures and predicate argument
structure are restored, the generalized helpers have distinct
`coefficientUniverse` names, and the existing equivalence lemmas are retained.
Four explicit callers use the generalized names. No new `sorry` is introduced.

Validation on the isolated server checkout, using `tools/lean_file.sh` (nice 19,
two Lean threads, 60 seconds per file, sequential):

- The before-fix duplicate import was reproduced.
- The repaired duplicate-import probe, `ProjectionMateExact`, and
  `SfIntegralReductionTower` pass.
- All four adjusted callers compile.
- One consumer imports all 13 recorded statement-prerequisite modules and checks
  both `AlgebraicGeometry.Etale.vectorBundleIntegration` and
  `WeilConjectures.finiteCoefficientTwist`: pass.
- All eight `test_nt_source_overlay` / `test_nt_compile` tests pass, including the
  transitive published-import and old/new signature regressions.

Original copies of every modified existing file are kept as
`.maint-NF-vector-purity-1792139145.bak`. The validated checkout is
`/home/ubuntu/weil-newtargets-maint-NF-vector-purity-1792139145`.
The maintenance report and diagnostic logs are on the launcher under
`/home/ubuntu/weil-launcher-all/maint/NF-thm-amb-vector-bundle-purity-1792139145`.

Next worker: continue stage 2 using the recorded prerequisites and the normal
`scompile.py` wrapper. Start probes with `module`. Do not restate the prerequisite
nodes or weaken the item to avoid its coefficient comparison. The theorem itself
has not been written by maintenance. The failure counters remain evidence only;
they must not suppress dispatch.
