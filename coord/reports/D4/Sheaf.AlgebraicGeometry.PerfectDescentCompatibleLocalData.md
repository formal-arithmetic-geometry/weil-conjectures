## What changed

Prepared a strict two-step decomposition of
`AlgebraicGeometry.perfect_descent_compatible_local_data` without changing its signature.
The item's proof first proves that `f ≫ s` has the required local finite-presentation,
quasi-compactness and quasi-separatedness properties, obtains common-stage local models,
and then applies eventual overlap/adjoint compatibility and composes the index inequalities.
New modules are `Sheaf.AlgebraicGeometry.PerfectDescentCommonLocalModels` and
`Sheaf.AlgebraicGeometry.PerfectLocalModelsEventuallyCompatible`.

The first new statement supplies only compact covering opens, perfect local objects and
local limit isomorphisms. It supplies no overlap or adjoint datum. The second assumes
prescribed local objects and their comparisons, supplies no descent-on-opens hypothesis,
and handles overlap descent and compatible adjoints. Neither restates the original theorem.

The resumed worker verified that the shared baseline now supplies the previously missing
`Sheaf.AlgebraicGeometry.PerfectOpenGluingData.olean`. Validation uses that shared baseline
and only the three delivered Lean modules; no substitute dependency is included.
Nothing was pushed.

## Proved and sorry left

Closed the one original syntactic hole by a two-step decomposition:
`AlgebraicGeometry.perfect_descent_compatible_local_data`
(node `lem-pc-perfect-descent-compatible-local-data`). This is a decomposition, not a proof without remaining dependencies.
Two strictly smaller intermediate statements remain named holes; the net hole count is +1.

Two new holes, each a named theorem with source and proof in words:

- `AlgebraicGeometry.perfect_descent_common_local_models`
  (`lem-pc-perfect-descent-common-local-models`).
- `AlgebraicGeometry.perfect_local_models_eventually_compatible`
  (`lem-pc-perfect-local-models-eventually-compatible`).

No sorry remains syntactically in the item's module. No definition was added or changed.

## No longer needed

The item no longer directly imports `Sheaf.AlgebraicGeometry.PerfectDescendMorphisms`,
`Sheaf.AlgebraicGeometry.DerivedPullbackPerfect`,
`Sheaf.AlgebraicGeometry.DerivedAdjoint`,
`Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction`, or
`Sheaf.AlgebraicGeometry.DerivedPullbackOpenRestrictionUniverses`.
Their nodes remain needed in the two subarguments and are imported there.
No mathematical dependency or module is pruned from the transitive argument.
The unchanged public imports remain necessary for the item's signature.
No global gluing or global descent result is used.

## Where the brief, the DAG or earlier work was wrong

The previous attempt was blocked because the compiled-library baseline omitted
`Sheaf.AlgebraicGeometry.PerfectOpenGluingData`. That artifact is now present in the shared
baseline; no baseline source or artifact is included as a workaround.
`tools/blueprint_refs.py ancestor lem-pc-perfect-descent-compatible-local-data` returns
`None` because the existing node uses a module name in `created.item`. The new nodes
therefore follow the item's explicit nearest ancestor `lem-pc-rf-perfect-base-change`.
No target, definition, existing statement, chapter or unit route was changed.
The unit record has empty realized fields, so no realized unit step was bypassed.

The source read was Stacks Tag 09RF, its two-open induction before Tag 08DG:
https://stacks.math.columbia.edu/tag/09RF . The statement's open-union form is retained.
LeanFinder returned only generic derived-category representation theorems; Loogle returned
adjunction Hom-equivalence tools; Mathlib grep and project searches found no duplicate.
LeanSearch returned Internal Server Error, recorded as unavailable in searches.jsonl.

Edge cases checked mathematically: empty or equal opens, disjoint opens (empty overlap),
an empty stage scheme, the zero complex, and a preorder that is not antisymmetric.
The fixed initial index ensures nonemptiness, and the source constructions work on empty
opens without requiring either covering member or its intersection to be nonempty.

## New nodes

`lem-pc-perfect-descent-common-local-models` makes precise only the first sentence of the
local induction: separately descend the restricted objects, then move to a common stage.
It is weaker in conclusion than compatible local data and does not need a colimit proof.

`lem-pc-perfect-local-models-eventually-compatible` makes precise the remaining local
construction from already prescribed perfect models and limit comparisons. It is independent
of the descent-on-opens predicates and of perfectness of E; it uses Tag 09RE on the overlap,
then Tags 079W and 08FE for compatible adjoints. The two nodes inherit the item's unit and
chapter. No change record or forced adaptation is needed.

Validation (2026-10-13, resumed attempt): both intermediate statement modules passed
isolated baseline compilation (26.5 seconds and 21.2 seconds). The common-model
module generated its artifact in two dry runs (51.3 and 51.9 seconds), but
`PerfectLocalModelsEventuallyCompatible` repeatedly exceeded the 60-second limit
when generating its artifact, so no full baseline-only dry run printed OK.
The machine load average was 145.46 during the failures; the cause is not established.
A compact local-let version of the statement and removing unused proof-only imports
did not resolve the timeout. Both experiments were reverted; the source and DAG retain
the original, independently type-checked reduction and its planned proof imports.
No baseline substitute was used in this resumed attempt. Nothing was pushed.

Final required dry run on the restored files: `COMPILE FAILED (local)`;
`PerfectDescentCommonLocalModels` exceeded the 60-second limit.
Status: BLOCKED by repeated artifact-generation timeouts, despite successful
isolated type-checks. The preserved draft is not certified READY.

## Second reading by D4

1. **Statements and interfaces:** Compared the delivered target module with the repository version. The target theorem signature is byte-for-byte unchanged; only its proof body and proof-only imports changed. The two added theorem statements are strictly smaller reductions and retain the required hypotheses and conclusions described by their DAG nodes. Verdict: pass.

2. **Proof and compilation:** Compiled all three sandbox modules with `lcompile.py --all`; all completed successfully (common local models, eventual compatibility, and the target module). The target has no syntactic `sorry`; the only remaining holes are the two named split-off theorems, each documented and represented by a node. No definitions contain `sorry`, and no forbidden declarations were added. Verdict: pass.

3. **DAG and sources:** Checked the three node files against the Lean declarations, including statements, proof dependencies, source locations, and `proof_origin`. The target node records the two-step reduction, and each split node records its source and proof plan. Verdict: pass.

4. **Pruning and route:** The target no longer imports the five modules used only by the former monolithic proof; those dependencies remain imported by the eventual-compatibility split where needed. The proof follows the unit's recorded route through common local models and eventual compatibility. No target or definition was changed. Verdict: pass.

5. **Edge cases and duplication:** Reviewed the split statements for empty/equal/disjoint opens, empty stages, zero complexes, and non-antisymmetric preorders as documented above. Repository and Mathlib searches found no duplicate declaration or shorter applicable theorem. Verdict: pass.

Changed during second reading: reran the full sandbox compilation after the earlier timeout report; it now completes cleanly. No source or DAG edits were needed beyond this report section.
