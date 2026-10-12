## What changed

Replaced the fixed-degree restatement by the actual filtered-colimit proof in
`Sheaf.AlgebraicGeometry.PullbackIsoTorsionColimit`. Existing signatures and docstrings
are unchanged. Added two plain proof imports: `EtaleCohomologyFilteredColimit` and
`EtaleSheafHExtDerivedComparison`. Removed the proposed degree module and its new node.
Updated the item's proof plan and dependencies to match the completed reduction.

## Proved and sorry left

Proved `AlgebraicGeometry.Etale.pullback_cohomology_bijective_of_torsion_colimit`:
1 of 1 original obligations; 0 split off; no `sorry` remains in the delivered module.
The proof still depends on the existing open filtered-cohomology theorem
`AlgebraicGeometry.Scheme.etaleCohomology_isColimit_of_isFiltered`
(node `lem-weil-pbc-cohomology-filtered-colimit`). This is a reduction to an existing
proper part of the argument, not a claim that all transitive dependencies are closed.

## No longer needed

Removed `PullbackIsoTorsionColimitDegree` and its unlanded node
`lem-weil-pbc-pullback-iso-torsion-colimit-degree`: introducing q merely restated the item.
No original public imports were removed. All three trial Mathlib imports were removed
because the required infrastructure is already available through the retained imports.

Old proof dependencies no longer used directly:
- `lem-weil-pbc-inverse-image-preserves-colimits` / `EtaleInverseImageColimits`:
  replaced by the proved upstream left-adjoint instance and the Mathlib leaf
  `lem-weil-pbc-left-adjoint-preserves-colimits`.
- `lem-weil-pbc-cohomology-pullback-functorial` / `EtaleCohomologyPullbackFunctorial`:
  replaced by the proved upstream `cohomologyMap_map` in the existing statement import.
- `def-weil-directed-colimit-abelian-groups`: no element representatives are selected;
  Mathlib's colimit universal-property isomorphism lemma supplies the conclusion.

These are local dependency removals; other targets may still need these modules.
All other original proof dependencies remain used. The unit's realized route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The first worker's degree theorem was logically equivalent to the original theorem:
introducing q leaves exactly the same hypotheses and conclusion. Its remaining sorry
contained the entire argument, so the split was not progress. The original plan is
sound, but the generic colimit-isomorphism step is already implemented by Mathlib.
The inverse-image colimit and cohomology naturality special-purpose open statements
can also be bypassed using their proved upstream ingredients below the unit level.

Independent searches used different descriptions: Loogle queried
`CategoryTheory.Limits.isIso_app_coconePt_of_preservesColimit`; LeanFinder searched
for a natural transformation invertible at a colimit point when its components are
invertible and both functors preserve the colimit. Both found the exact Mathlib lemma.
Local rg confirmed the proved Ext comparison, upstream `cohomologyMap_map`, and
`H_map_isColimit_of_isFiltered`. The latter is an available alternate elementwise
route, but the direct functor/cocone proof uses fewer intermediate results.

## Second reading by P1

1. Compared the delivered module with the repository using diff. The sole original
   theorem's signature and docstring are byte-for-byte unchanged; no definitions,
   public imports, targets, or other modules changed. Verdict: pass after repair.
2. Compiled the original submitted two modules and the repaired single module through
   lcompile.py. No forbidden declarations or definition sorries occur. A scratch copy
   checks the original theorem with #print axioms; its only extra dependency is the
   permitted sorryAx from the existing filtered-cohomology theorem. Verdict: pass as
   a stage-3 reduction, with the transitive open dependency explicitly reported.
3. Rejected and removed the fixed-degree split because it was the whole statement
   under another name. No new statements or nodes remain. The actual proof establishes
   kernel annihilation and the induced colimit isomorphism. The zero sheaf, empty
   schemes, degree zero, and n=1 require no exception: the category is nonempty,
   kernel cancellation is valid, and the colimit argument works in all degrees.
   Verdict: pass after repair.
4. Used existing comparison/filtered-colimit declarations, upstream naturality and
   inverse-image adjunction, and Mathlib's generic colimit-isomorphism theorem.
   Removed redundant proof imports and listed every old dependency no longer used.
   Checked dag/units/sk-thm-p1.json realized: no unit statement or step is bypassed;
   the strict-henselian comparison's torsion-colimit route remains. Verdict: pass.
5. Read the original node and replaced only proof, proof_deps and proof_origin to
   record the actual kernel diagram, AsSmall reindexing, natural Ext comparison,
   left-adjoint preservation, and isomorphism at the cocone point. The original
   statement and lean signature record are unchanged. Verdict: pass.

Changes made during second reading: removed the equivalent fixed-degree split;
completed the real reduction without new obligations; minimized proof imports;
updated the DAG proof metadata and this report. Final local and server validation
is performed by deliver3.py before pushing.
