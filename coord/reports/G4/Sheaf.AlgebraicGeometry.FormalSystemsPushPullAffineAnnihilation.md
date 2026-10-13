## What changed

Completed `AlgebraicGeometry.formalSystemsPushPull_affine_annihilation` in the item module. The proof uses the completed affine comparison, the affine coherent support radical criterion, and Noetherian ideal finite generation. It introduces two private commuting-square transport lemmas for annihilators of kernels and cokernels. Added the support criterion module (fully proved) and the completed affine comparison module (one named theorem remains a documented `sorry`). Updated the target node proof and proof dependencies to match this route.

## Proved and sorry left

Closed one original hole: `AlgebraicGeometry.formalSystemsPushPull_affine_annihilation`. Added one hole: `AlgebraicGeometry.formalComparison_completed_affine_model`. This is a decomposition, with net zero holes closed, rather than an unconditional proof of the item. Proved `AlgebraicGeometry.coherentAffineMap_support_radical`. The new declaration `AlgebraicGeometry.formalComparison_completed_affine_model` remains `sorry`; its node is `lem-weil-pbc-formal-comparison-completed-affine-model`.

## No longer needed

No repository import was removed. During second reading, removed redundant imports `Mathlib.RingTheory.Ideal.Operations` and `Mathlib.RingTheory.Spectrum.Prime.Topology` from the new support module, and `Mathlib.RingTheory.Finiteness.Ideal` from the delivered target proof additions; recompilation of the full three-module set passed. The following old target proof dependencies are no longer used directly by the target proof:

- `lem-weil-pbc-theorem-formal-functions` (retained in the completed-comparison proof plan).
- `lem-weil-pbc-coherent-formal-modules-affine` (retained in the completed-comparison proof plan).
- `lem-weil-pbc-formal-systems-pullback` (retained in the completed-comparison proof plan).
- `lem-weil-pbc-noetherian-completion-flat` (retained in the completed-comparison proof plan).
- `lem-weil-pbc-adic-completion-mod-power` (retained in the completed-comparison proof plan).
- `lem-pc-flat-base-change-cohom` (retained in the completed-comparison proof plan).
- `def-pc-module-pullback` (retained in the completed-comparison proof plan).
- `lem-weil-pbc-quasi-coherent-finite-type-affine` (retained in the completed-comparison proof plan).
- `pqf-lem-coherent-ft-locnoeth` (retained in the completed-comparison proof plan).
- `lem-weil-pbc-formal-completion-fully-faithful-proper` (retained in the completed-comparison proof plan).
- `lem-pc-coherent-hi` (retained in the completed-comparison proof plan).
- `lem-weil-pbc-coherent-kernel-cokernel-locnoeth` (replaced by the proved affine localization/support argument).
- `lem-weil-pbc-coherent-support-power-ideal-kills` (replaced by the proved affine localization/support argument).

These are removals of direct DAG edges, not claims that their modules leave the targets’ import closure. No module is claimed pruned.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox attempt had a complete-looking proof but its support module did not compile: rewriting a local `let Q` with `rw [Q]` is invalid. Replacing it with `dsimp [Q] at hq` followed by the support lemma fixes the issue. The original target node listed a much larger dependency set than the compiled proof uses; its proof dependencies were pruned accordingly.

## New nodes

`lem-weil-pbc-formal-comparison-completed-affine-model` records the remaining completed-affine comparison theorem and its documented proof source. `lem-weil-pbc-coherent-affine-map-support-radical` records the fully proved affine support/annihilator theorem. Both node files are under `dag/nodes/sec-proper-base-change/`.

## Earlier second reading (a previous round; superseded)

The item module and both new nodes were compiled together. The target statement is unchanged. The completed affine comparison is a strict intermediate statement, and the support radical result is a strictly lower theorem; the target proof combines them with explicit kernel/cokernel transport rather than restating the target.

## Second reading by G4

1. **Visible declarations and statements.** I compared the delivered target module with the repository version. The target theorem signature is byte-for-byte unchanged; only proof-local imports, private transport lemmas, and the proof body were added. The two new modules contain the declarations recorded by their DAG nodes, and no existing declaration was weakened or given extra hypotheses. Verdict: pass.

2. **Compilation and proof status.** I compiled all three sandbox modules with `lcompile.py`; the target and support theorem compile without errors. The only remaining `sorry` is the named theorem `AlgebraicGeometry.formalComparison_completed_affine_model`, exactly the split-off theorem listed above. No `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` occurs. The target's axioms include `sorryAx` only through that documented dependency; the other proof is kernel-checked. Verdict: pass, with the documented comparison hole remaining.

3. **Truth and strength of split statements.** `coherentAffineMap_support_radical` is a strict affine support criterion: invertibility off the closed set forces the ideal into the annihilator radicals of the section kernel and cokernel. `formalComparison_completed_affine_model` is the lower construction statement needed by the target and does not restate the target's annihilation conclusion. Both statements agree with their node files, have source/proof docstrings, and are not duplicate library declarations. Verdict: pass.

4. **Shortest route and pruning.** The target proof uses the completed affine comparison, the affine support criterion, finite generation over a Noetherian completion, and two private kernel/cokernel square-transport lemmas. The target node's `proof` and `proof_deps` match these uses. The earlier direct formal-functions/base-change route is encapsulated by the split comparison theorem and is listed as no longer needed. The unit record `sk-thm-p1` remains unchanged and its realized route is respected. Verdict: pass.

5. **DAG and delivery metadata.** The target and both new node records agree with the Lean module/declaration names, statements, source, chapter, and unit. I expanded the still-open comparison node’s proof plan and dependencies to retain the base-change, pullback, proper full-faithfulness and coherence steps from the old plan; the support node now records the coherence/quasi-coherence criterion actually used. The support proof's prior invalid `rw [Q]` pattern was repaired to `dsimp [Q] at hq`; the report records this correction. Verdict: pass.

I added this second-reading record, corrected both new nodes’ proof/dependency descriptions, recorded fresh searches, made the hole accounting and direct-edge pruning explicit, and removed three redundant imports as listed above. No Lean statement, definition, or proof body was changed during this reading. The prior worker’s already-present support proof repair is not attributed to this reading. The source was checked against Stacks Tag 088B, especially its completed-base reduction and algebraization paragraphs. The remaining construction is substantial and was not closed in a few minutes. Edge cases checked include the empty affine/zero ring, J equal to the unit ideal, K equal to zero or the unit ideal, and the identity proper map; none requires an additional hypothesis. Both new declarations are propositions, and no definition selects arbitrary data from their unproved existence statements.
