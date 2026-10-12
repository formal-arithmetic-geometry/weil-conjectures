## What changed
Split the proof into two strictly smaller public lemmas: finite-stalk torsion cocone existence and preservation of its mapped cohomology cocones. The target theorem is proved by applying these lemmas. Added imports for both modules.

## Proved and sorry left
`exists_generic_torsion_finite_stalk_cohomology_colimit` is proved by composition. The new lemmas `exists_generic_torsion_finite_stalk_colimit` (lem-sc-generic-torsion-finite-stalk-colimit-finite) and `generic_torsion_cohomology_colimit` (lem-sc-generic-torsion-finite-stalk-colimit-cohomology) retain sorry proofs for parallel workers.

## No longer needed

The old proof-only imports `Sheaf.AlgebraicGeometry.AbelianSheavesGModules`,
`Sheaf.AlgebraicGeometry.Sites.EtaleSheavesGsetsPoint`,
`Sheaf.AlgebraicGeometry.EtaleDirectedCohomologyColimit`, and
`Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison` are no longer used by the
factored proof. Their corresponding old proof dependencies are replaced by the two
new split-node dependencies; the unit route itself is retained.

## Where the brief, the DAG or earlier work was wrong
The original proof requires two substantial independent constructions; they were split into named intermediate statements.

## New nodes
`lem-sc-generic-torsion-finite-stalk-colimit-finite` and `lem-sc-generic-torsion-finite-stalk-colimit-cohomology`.

## Second reading by N1

1. **Statements and accidental changes.** I compared the delivered target module with the repository version. The theorem signature and all existing declaration statements are byte-for-byte unchanged; only proof imports and the target proof were changed. The two added declarations have the signatures recorded by their nodes.

2. **Compilation and axioms.** `lcompile.py --all` compiles all three delivered modules. The target proof contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the only remaining `sorry`s are the two named split-off theorem proofs, each with a source/docstring and node. The split-off theorems are intentionally open construction lemmas, so their downstream use carries `sorryAx` until proved.

3. **Split-off statements.** `exists_generic_torsion_finite_stalk_colimit` states exactly the finite-stalk torsion cocone needed by the target, and `generic_torsion_cohomology_colimit` states exactly preservation of its mapped cohomology cocones. They are strictly smaller than the target and are not duplicate restatements. Searches recorded in both nodes found no Mathlib or existing-library declaration supplying these results.

4. **Pruning and route.** The target proof takes the shortest available local route by applying the two split lemmas. The old proof-only imports are replaced by the two modules that actually provide those lemmas; no additional imported node is required, so no old proof dependency is pruned beyond that replacement. The unit route remains represented by the target node and its two decomposition steps.

5. **DAG agreement.** The target node's `proof` and `proof_deps` now name exactly the two declarations used by the Lean proof. The new nodes' Lean records, statements, source, proof origin, and split status agree with their modules.

**Changes made.** Added the target-node proof metadata update, retained the two explicit split modules and nodes, and added this second-reading record. No mathematical statement or definition was changed.
