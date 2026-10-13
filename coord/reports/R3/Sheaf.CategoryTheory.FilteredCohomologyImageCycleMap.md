## What changed

Proved `CategoryTheory.DecreasingFiltration.cohomologyImage_cycle_map` in
`Sheaf.CategoryTheory.FilteredCohomologyImageCycleMap`, preserving its statement and visibility.
The argument identifies filtered cycles with an intersection, computes their homology image
by naturality, and computes the inverse image using the cokernel kernel and modularity.

Repair of the returned delivery: removed the duplicate private declarations
`pullback_exists_isCokernel`, `pullback_exists_iso`, and `subobject_modular`.
Added the proof-only `import all Sheaf.CategoryTheory.FilteredNormalizedQuotientPresentation`
to reuse those existing private helpers. Also removed the matching `map_pullback_mono`
helper and reused the existing one. No dependency module or public interface was changed.
Updated the node's proof and dependencies to record this reuse.

## Proved and sorry left

Closed the sole original hole:
`CategoryTheory.DecreasingFiltration.cohomologyImage_cycle_map`
(node `new-cohomology-image-cycle-map`). One hole closed, zero holes added;
no `sorry` remains in the delivered module. The five remaining private helpers are proved.
This is a proof, not a decomposition.

The repaired module compiles without errors or warnings using `lcompile.py`.
The delivery dry run also checks every added declaration's axioms.

## No longer needed

Removed four duplicate helper proofs listed above. Replaced the previous delivery's direct
proof imports of `WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits` and
`WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject` with the existing helper module's
proof-only import; the required categorical infrastructure is available through it.
No original imports or DAG dependencies were removed, and no DAG modules are pruned.
The second reading also removed the duplicate `exists_image` helper, reusing the proved
private helper of `FilteredComplexFirstPageCyclesBoundaries` through a proof-only
`import all`. Its public first-page theorem is not applied.
`FilteredNormalizedQuotientPresentation` is now required for its proved private helpers;
its public quotient theorem is not applied. The original public import of
`FilteredCohomologyImage` supplies the definition used in the statement.

## Where the brief, the DAG or earlier work was wrong

The previous delivery copied three helper statements already present word for word in
`FilteredNormalizedQuotientPresentation`, causing `import_prune_check.py` to refuse landing.
The helpers are private, but `import all` makes them reusable without changing visibility.
The repaired proof imports and uses them instead. The fourth matching restriction helper
is reused in the same way. The previous second reading described the copied proofs as
acceptable; a fresh second reading is needed for this repaired delivery.


## Second reading by R3

1. **Interface unchanged — pass.** Read the full repository/sandbox module diff before
   delivery. The sole existing declaration's signature, visibility and docstring are
   byte for byte unchanged. Only its proof, private proved helpers and proof-only imports
   are added. No definition, target statement or change record is involved.
2. **Kernel proof — pass.** Compiled the repaired module locally without errors or
   warnings. Compiled a scratch copy with `#print axioms` for the main theorem and all
   five local helpers: each uses exactly `propext`, `Classical.choice`, and `Quot.sound`.
   There is no `sorry`, forbidden declaration, or data selected from an unproved theorem.
   Read the reused cokernel comparison, modularity and restriction proofs in their source.
3. **Split statements and duplication — pass after repair.** No statements are split
   off and no holes are added. A fresh `rg` search over Sheaf, upstream and Mathlib found
   `exists_image` already proved in `FilteredComplexFirstPageCyclesBoundaries`. Removed
   the local duplicate and reused it with a proof-only `import all`. The remaining local
   inverse-image-of-bottom identity has equivalent private helpers in half-plane modules;
   importing their exact-couple convergence infrastructure solely for this elementary
   specialization would add irrelevant dependencies. Its proof uses the existing factor
   criteria directly. Checked zero/top filtration steps, zero differential, and zero
   homology: the cycle image and inverse-image formulas retain the required identities.
4. **Route and pruning — pass.** Read top down: the cycle image is proved by kernel
   lifting and homology naturality; the inverse image follows from the cokernel kernel
   identity and modularity, with no finiteness assumptions. The two public quotient/page
   theorems of the helper modules are not used. Both proof-only helper imports are needed;
   the original public import supplies the statement's cohomology-image definition.
   Every old proof dependency remains used, so there are no old nodes to prune.
   Read `dag/units/sk-prop-av-pqf-finite.json`: its existing `realized` lists are empty;
   this cycle-map node is a below-unit auxiliary and the delivery changes no unit route.
5. **DAG agrees — pass after repair.** The node's steps describe the cycle lifting,
   cokernel inverse-image and modularity argument actually used. Added the first-page
   module's node to the image-composition step and `proof_deps`, explicitly noting that
   only its proved private helper is reused. The dependencies are the union of step
   uses. No new nodes or changed statements are delivered.

Second reading changed: removed the additional duplicate `exists_image` declaration,
added its existing helper module as a proof-only import, and updated the DAG and report.
One original hole closed, zero holes added; five local helpers are fully proved.
