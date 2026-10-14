## What changed

Repaired the landed import graph. `ScalarExternalCupModuleComparison` no longer directly
imports `Sheaf.Paper.ModuleCohomologyCupProduct`; it publicly imports
`ScalarCupModuleCupCompatibility`, whose public import provides the canonical
`IsModuleCupProduct` declaration. This removes the duplicate exposed local-instance
collision between `ModuleCupKInjectiveTarget` and
`GlobalTensorPullbackMonoidalNormalization` when the module is imported after the
latter. The theorem statements and proof bodies are unchanged.

## Proved and sorry left

No theorem hole was added or closed in this repair. The existing external theorem
remains proved from the two named prerequisite theorems, which remain `sorry` as in
the landed delivery:

- `AlgebraicGeometry.Scheme.Modules.scalarCup_moduleCup_compatibility`;
- `AlgebraicGeometry.Scheme.Modules.scalar_moduleCohomologyPullback_comparison`.

## No longer needed

The direct proof-only import of `Sheaf.Paper.ModuleCohomologyCupProduct` in
`ScalarExternalCupModuleComparison` is no longer needed; its canonical declaration is
provided through the public `ScalarCupModuleCupCompatibility` import. No node or
statement dependency is removed.

## Where the brief, the DAG or earlier work was wrong

The landed external module imported `ModuleCohomologyCupProduct` both directly and
through `ScalarCupModuleCupCompatibility`. In the combined global environment this
caused Lean to re-enter `ModuleCupKInjectiveTarget` after
`GlobalTensorPullbackMonoidalNormalization` and reject the duplicate exposed local
instance `AlgebraicGeometry.Scheme.Modules.instSymmetricCategorySheafOfModulesOpensCarrierCarrierCommRingCatToRingedSpaceModuleRings_1`.
Using the public prerequisite module as the single import path preserves the exact
canonical predicate and avoids that collision.

## New nodes

None.

## Second reading by XRa2c5451bd4aff80a

1. **Source and interface comparison.** I compared every delivered Lean module and DAG node with the repository baseline and the returned `delivery.diff`. The three declarations retain their intended signatures and target statements; this repair changes only the external module import graph. Verdict: pass.

2. **Compilation and proof safety.** I compiled each touched Lean file individually with `/home/ubuntu/weil-launcher/lcompile.py`; all three completed successfully within 60 seconds with no errors or warnings. The only remaining `sorry`s are the two named split-off prerequisite theorems, each documented and represented by its DAG node. No `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or kernel-skip workaround was added. Verdict: pass.

3. **Mathematics and targets.** The external theorem still reduces `externalCup` to `scalarCup_moduleCup_compatibility` and rewrites both scalar pullbacks through `scalar_moduleCohomologyPullback_comparison`; no hypothesis, conclusion, or definition was weakened. The two prerequisite statements remain exactly the intended comparison lemmas. Verdict: pass.

4. **Pruning and DAG/unit consistency.** The removed direct proof-only cup-product import is recorded here and the external node’s proof dependencies match the declarations used by its proof. The three nodes retain the `sk-prop-av-cube` unit route; no unit step was bypassed and no node was unnecessarily added or removed. Verdict: pass.

5. **Importer repair.** I verified that `ScalarExternalCupModuleComparison` receives `IsModuleCupProduct` through the single public `ScalarCupModuleCupCompatibility` path, eliminating the duplicate exposed instance collision reported by the failed landing. The change is recorded in `coord/changes/scalar-external-cup-module-comparison.md`. Verdict: pass.

**Changes made during second reading:** changed that record's status to `open` for stage-3 delivery validation and added this independent review section. No Lean theorem or DAG statement was altered.
