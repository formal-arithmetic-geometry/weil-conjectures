## What changed

The existing signature and public imports of `AlgebraicGeometry.diagonalConormal_affine_sections` are unchanged. Its proof obtains one normalized derivation from `exists_diagonalConormalDerivation`, applies the fixed-derivation affine calculation, and proves that the resulting equivalence works for every normalized derivation using open-section uniqueness.

Added `DiagonalConormalAffineSectionsBase` for the remaining affine calculation for a supplied normalized derivation, and `DiagonalConormalAffineSectionsUnique` for the proved uniqueness on every open. Only `DiagonalConormalDerivation` is publicly imported by these modules. The affine conormal, base-change and upstream sectionwise-kernel modules are proof-only imports. No definition or existing statement changed, and no change record is needed.

## Proved and sorry left

Closed the existing hole `AlgebraicGeometry.diagonalConormal_affine_sections` (node `lem-sc-diagonal-conormal-affine-sections`). Added one hole: `AlgebraicGeometry.exists_diagonalConormal_affine_sections_base` (node `lem-sc-diagonal-conormal-affine-sections-base`). It supplies coordinates for one given normalized derivation; the target's existence of a normalized derivation and independence of its choice are handled outside that hole. Its docstring contains the full natural-language affine argument.

`AlgebraicGeometry.diagonalConormal_affine_sections_unique` (node `lem-sc-diagonal-conormal-affine-sections-unique`) has a complete Lean proof, with no `sorry`. The first worker left it open; the second reader closed it and generalized it to every open by removing the unused affine-chart assumptions.

This delivery is a decomposition: one old hole closed and one new hole added, net zero explicit holes. The target still rests on the open affine calculation and the existing normalized-derivation existence theorem. It is not an axiom-free completion of the target. No hole was added inside a definition and no data definition was added.

## No longer needed

Removed the item's direct proof imports `Sheaf.AlgebraicGeometry.AffineConormalSections` and `Sheaf.AlgebraicGeometry.BaseChangeConventions`; they are retained as proof-dependency imports in the new fixed-derivation affine calculation module. The old direct node dependencies `def-sc-diagonal-conormal`, `def-pc-base-change`, `lem-weil-pbc-affine-conormal-sections`, and `lem-sc-kahler-differentials-diagonal-ideal` move under that calculation. `lem-sc-diagonal-conormal-derivation-exists` remains a direct dependency. All old dependencies remain reachable through the new proof dependencies, so no old dependency module is globally pruned. No unit route or unit realization changes.

## Where the brief, the DAG or earlier work was wrong

The first report called a one-hole-to-two-hole split a proof and claimed the base existential was strictly weaker than the original. That base statement bundled existence of a normalized derivation with almost all of the target's affine content. The second reader separates those responsibilities: normalized-derivation existence comes from the existing declaration, the new affine hole takes a supplied normalized derivation, and independence is proved using an existing kernel-section theorem.

The first delivery omitted the existing item's DAG proof update, copied node signatures containing literal Unicode escape sequences rather than verbatim Lean, publicly imported two proof-only modules, and supplied only abbreviated proof docstrings. All were repaired. The actual source calculations were checked against [Stacks 08S2](https://stacks.math.columbia.edu/tag/08S2), [01KJ](https://stacks.math.columbia.edu/tag/01KJ), and [01R3](https://stacks.math.columbia.edu/tag/01R3).

## New nodes

`lem-sc-diagonal-conormal-affine-sections-base`: the affine coordinate calculation for a supplied normalized derivation, with an explicit restriction, cotangent quotient, class-map and differential-formula proof plan. It does not construct the normalized derivation or establish independence. The remaining `sorry` is exactly its named theorem.

`lem-sc-diagonal-conormal-affine-sections-unique`: proved uniqueness of the normalization on every open, using `Scheme.Modules.range_map_kernelι` and Mathlib's scheme section-map composition. No affine or separatedness assumptions are needed. It is true even on the empty open.

Both new nodes have their complete statements, literal Lean signatures, provenance, blueprint ancestry, chapter/unit, creation records and three independently executed search kinds. Existing-node edits are restricted to proof-owned fields.

## Second reading by T2

1. Compared the delivered item with the repository using `diff -u`. The existing theorem signature, visibility, section variables, docstring and public imports are byte for byte unchanged. Only its proof and proof-only imports differ. There are no adapted existing modules or changed definitions. Verdict: pass.
2. Compiled all three modules in import order through `lcompile.py`, with no errors or warnings. The only delivered `sorry` is the listed named base theorem. Scanned for forbidden declarations and checked `#print axioms` for all three declarations in a scratch module: only the permitted standard axioms and, for open dependency proofs, `sorryAx` occur. No data is chosen into a definition from mere unproved existence. Verdict: pass as a decomposition, not a closed target.
3. Read both new statements and their proofs/plans top down. Proved uniqueness directly from the existing upstream sectionwise-kernel lemma; this avoids an unnecessary new hole. Checked empty opens, the identity morphism (zero differentials/conormal), and nonseparated morphisms: the affine calculation only needs the restricted diagonal to be closed on U ×_V U, and the uniqueness proof uses no closedness. LeanSearch was independently attempted and returned Internal Server Error; independent leanfinder, loogle and grep searches found ring-level differential tools and section-map tools, but no independent scheme-level affine equivalence. Searched the library for conormal, diagonal, kernel-section and affine-differential variants: the comparison theorem depends on this item, while relative differentials concern a different sheaf. The supplied-D base lemma isolates the affine argument; the target combines it with existing existence and proved independence. Verdict: pass.
4. Removed redundant direct proof imports from the item and corrected public proof-only imports in the new base module. The complete old direct dependency list and its new placement are recorded above. Read `dag/units/sk-thm-picard-duality.json`: its realized fields and route stay unchanged; this is a below-unit affine calculation. Verdict: pass; no globally pruned modules.
5. Updated the existing item's proof, proof_deps and proof_origin to the actual Lean reduction. Rewrote the base and uniqueness nodes for their final signatures, recorded the actual independent searches, and supplied complete natural-language proofs. Checked the dependency lists equal the union of the proof-step uses. Verdict: pass.

Changes in this second reading: proved and generalized uniqueness, narrowed the base lemma to a supplied derivation, used existing derivation existence explicitly in the target, corrected import visibility and redundant imports, repaired node signatures and dependencies, expanded proof documentation, and corrected the progress accounting.

The initial dry run required the separate LeanSearch search category; both queries were executed and the unavailable-service results recorded. The corrected dry run is required to pass before pushing.
