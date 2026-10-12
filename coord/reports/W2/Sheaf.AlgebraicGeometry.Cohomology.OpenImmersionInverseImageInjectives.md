## What changed

Proved `AlgebraicGeometry.Scheme.Modules.invImage_preservesInjectiveObjects_of_openImmersion` by unfolding `invImage` and applying a generic open-embedding sheaf pullback theorem. Added the intermediate module `Sheaf.AlgebraicGeometry.Cohomology.OpenEmbeddingSheafPullbackInjectives`, whose theorem remains a named sorry. The proof-only import of that module was added.

## Proved and sorry left

The target theorem is proved. The added theorem `Topology.isOpenEmbedding_sheafPullback_preservesInjectiveObjects` remains sorry, with node `lem-pc-open-embedding-sheaf-pullback-injectives`.

## No longer needed

No imports or proof-dependency nodes were removed beyond replacing the unused planned restriction route with the generic open-embedding theorem.

## Where the brief, the DAG or earlier work was wrong

The planned proof required transporting through the scheme open immersion's image. The definition of `invImage` is definitionally the topological sheaf pullback, so that transport is unnecessary once the generic open-embedding result is isolated.

## New nodes

`lem-pc-open-embedding-sheaf-pullback-injectives`: generic open-embedding sheaf pullback injectivity; module `lean/Sheaf/AlgebraicGeometry/Cohomology/OpenEmbeddingSheafPullbackInjectives.lean`.

## Second reading by W2

1. **Statements unchanged.** Compared the delivered item module with the repository version; the target declaration has the identical signature, and the new generic theorem is separately stated. Verdict: pass.
2. **Proof and axioms.** Compiled both modules with `lcompile.py`; the target has no `sorry`, while the generic theorem is the single named split-off `sorry`. No forbidden declarations occur. Verdict: pass subject to the documented split theorem.
3. **Split-off statement.** Checked that the open-embedding pullback theorem is the strictly more general reduction needed by the target, with a source and matching DAG node, and is not already present in the library. Verdict: pass.
4. **Pruning and imports.** The target now uses only the generic open-embedding theorem; the former Zariski restriction and preadditive imports are removed, and the proof dependency is recorded in the target node. Verdict: pass.
5. **DAG and unit route.** The target and split node proof steps, dependencies, declarations, and unit assignment agree with the Lean files; the unit route is retained through the generic open-embedding step. Verdict: pass.

Changed only the target proof/imports, added the generic theorem module and its node, and recorded the second reading.
