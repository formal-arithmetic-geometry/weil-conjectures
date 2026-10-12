## What changed
Proved `TopCat.Sheaf.constantSubsheaf_normalized_core` directly from `hgen`.
Retained its compact opens and epimorphism, assigning every label the integer 1.
Updated the core node's proof, proof dependencies and origin to describe this route.
All declaration signatures and public imports remain unchanged.

## Proved and sorry left
Closed one original hole: `TopCat.Sheaf.constantSubsheaf_normalized_core`
(node `lem-sc-constant-subsheaf-normalized-core`).
The one original hole left is `TopCat.Sheaf.constantSubsheaf_normalized_completion`
(node `lem-sc-constant-subsheaf-normalized-completion`), unchanged.
Added no holes and no new declarations. This is a proof, not a decomposition.
Local compilation and the delivery dry run passed. The core proof also covers n=0:
the supremum of an empty family has no point, so its divisor condition is vacuous.
The bound holds for b=0 as well, since every label is 1.

## No longer needed
No imports, named nodes or modules were removed: the original core node had no
proof dependencies, and all three public imports are needed for its statements.
The clopen-refinement, Bezout, gcd-closure and stalk-bound arguments described in
its former plan are unnecessary for the written core structure. They may still
be needed for the remaining completion theorem and are not claimed as pruned.

## Where the brief, the DAG or earlier work was wrong
The core structure contains no compatibility between its labels and its epimorphism.
Consequently it follows immediately from the supplied finite epimorphic presentation,
without normalization of sections. The completion theorem has an independent
existential conclusion: it does not require using the input data d, so this direct
core proof does not invalidate that theorem. Its substantive normalization argument
remains open. No statement or definition was changed.
LeanFinder returned finite-type sheaf generator lemmas, but none giving the required
constant-value normalized presentation. The scripted grep had no matching result.
The Loogle query for Opens.mem_iSup did not resolve that name; local Lean compilation
did confirm it. The unit's realized statement and steps remain unchanged.

## Second reading by V1

1. I compared the sandbox module with the repository version. The signatures of `NormalizedPresentationData`, `constantSubsheaf_normalized_core`, and `constantSubsheaf_normalized_completion` are unchanged byte-for-byte; only the core proof and its local linter option differ. No definition or target statement changed.
2. The module compiles cleanly through `lcompile.py`; the core proof has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or other forbidden declaration. The remaining completion theorem is the only listed `sorry`. A scratch-copy `#print axioms` check shows exactly `propext`, `Classical.choice`, and `Quot.sound` for the core theorem; the completion additionally uses `sorryAx`.
3. The proof uses the existing `hgen` presentation, assigns the valid label `1`, and proves positivity, the upper bound, and the divisor condition. This is a true statement exactly matching the written interface, including the empty-index case. No new statement or split-off theorem was introduced.
4. The direct proof is shorter than the former normalization plan because the written core structure imposes no compatibility between labels and the map. All three public imports remain needed by the public structure and theorem signatures; no proof-only import was incorrectly made public.
5. The DAG node's proof, empty dependency list, and worker proof origin match the Lean proof, and the unit's realized route is unchanged. The delivery changes only the core proof, its local linter option, its node metadata, and the report. During this second reading I changed only the report; no proof repair was needed.
