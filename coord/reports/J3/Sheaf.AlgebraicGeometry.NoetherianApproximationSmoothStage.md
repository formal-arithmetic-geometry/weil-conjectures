## What changed
Added the affine-model and gluing intermediate theorems, each in its own module, and imported them into the item. The target theorem now applies the affine-model theorem and then the gluing theorem.

## Proved and sorry left
The target `AlgebraicGeometry.Scheme.NoetherianApproximation.exists_smooth_stage` is reduced by a complete Lean application. Two strictly stronger intermediate statements remain sorry: `exists_smooth_affine_model` (node `lem-sbc-noetherian-approximation-smooth-stage-affine-model`) and `smooth_stage_of_affine_models` (node `lem-sbc-noetherian-approximation-smooth-stage-gluing`).

## No longer needed
None; the original imports remain required by the stated route and the intermediate declarations.

## Where the brief, the DAG or earlier work was wrong
The prior attempt split off a theorem equivalent to the target. This delivery instead separates the affine finite-stage model (including a comparison isomorphism) from the subsequent locality/gluing step, so each remaining statement is a genuine component of the argument and strictly stronger than the target data it supplies.

## New nodes
`lem-sbc-noetherian-approximation-smooth-stage-affine-model` and `lem-sbc-noetherian-approximation-smooth-stage-gluing` are added under `dag/nodes/sec-smooth-base-change/`.

## Earlier second reading (a previous round; superseded)
The item and both new modules compile with `lcompile.py --all`. The target signature is unchanged. The two added statements are stronger intermediate components: the first supplies a smooth finite-stage model with comparison isomorphism, and the second performs the common-stage locality/gluing implication. A second worker should verify the exact mathematical strength and node metadata before landing.

## Second reading by J3

1. **Reading and interface diff.** Compared the delivered item module with the repository version. The target theorem statement is byte-for-byte unchanged; only its proof and proof-only imports were changed. The two added modules are new split-off declarations and are recorded by matching DAG nodes.
2. **Compilation and proof audit.** Compiled all three modules with `lcompile.py --all`; compilation succeeds. The target has no `sorry`; the only remaining `sorry`s are the two named split-off theorems, each with a public declaration, source docstring, and corresponding node. No forbidden `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by` was added.
3. **Statement review.** Checked both split-off statements against the target data. `exists_smooth_affine_model` supplies a smooth finitely presented model and an explicit comparison isomorphism, while `smooth_stage_of_affine_models` consumes exactly that data to obtain smoothness of the original pullback. They are genuine intermediate components and do not restate the target.
4. **Pruning and route.** The target proof follows the affine-model then gluing route. Removed the unused proof-only import `Sheaf.RingTheory.SmoothAlgebraFilteredColimitDescent` from the item; the new modules retain only imports used by their signatures or declarations. The unit route through affine descent and locality/gluing is preserved.
5. **DAG consistency.** Verified the two new node statements, declaration names, module paths, proof dependencies, source locations, chapter, and unit agree with the Lean declarations. No existing target node statement or definition was changed.

Changed after this reading: removed the unused smooth-algebra descent import from the item and added this review record.
