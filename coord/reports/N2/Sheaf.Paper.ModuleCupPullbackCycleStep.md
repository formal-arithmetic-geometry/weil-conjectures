## What changed

Replaced the deferred transport theorem with the existing `moduleCup_pullback_naturality` theorem from `Sheaf.Paper.CechCupPullbackCompat`, imported proof-only. The target theorem now closes directly by specializing that result to the two represented cohomology classes.

## Proved and sorry left

The sorry in `moduleCup_pullback_cycle_step` is closed. No new declarations or sorries were added.

## No longer needed

Removed the proof-only import `Sheaf.Paper.ModuleCupPullbackResolutionTransport`, the deferred transport module, its split node, and its change record. The previous transport split was unnecessary because the library already contains the stronger naturality theorem.

## Where the brief, the DAG or earlier work was wrong

The earlier proof introduced a transport statement duplicating the already available `moduleCup_pullback_naturality`; this was not a needed strictly smaller result. The DAG split node and associated change record have therefore been removed.

## Second reading by N2

1. I compared the delivered target declaration with the repository statement. The signature and all hypotheses are unchanged; only the proof body and proof-only import changed. Verdict: pass.
2. The file compiles with the local launcher, contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`, and the proof uses the existing naturality theorem. Verdict: pass.
3. No statement was split off. The proof uses the existing library theorem, which is stronger and directly specializes to the target. Verdict: pass.
4. The direct route is shorter and prunes the unnecessary transport module and node; the remaining proof-only import is minimal for the proof. Verdict: pass.
5. The node route is updated to use `moduleCup_pullback_naturality`; no new node remains and the unit route is preserved. Verdict: pass.

Changed the proof and import as described above, and pruned the unnecessary transport artifacts.

Change record: `coord/changes/module-cup-pullback-cycle-step.md`.
