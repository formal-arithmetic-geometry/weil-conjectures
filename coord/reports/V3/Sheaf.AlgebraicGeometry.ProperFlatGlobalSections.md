## What changed

Replaced the sole proof hole in `Sheaf.AlgebraicGeometry.ProperFlatGlobalSections`.
The proof applies `isIso_structureSheafMap_of_proper_flat_fiberwise`, then proves its
fibre hypothesis using `Scheme.globalSectionsRingHom_bijective_iff_geometricallyConnected`.
Properness of each fibre follows from `MorphismProperty.pullback_snd`. The canonical
residue-field structure map is the composite of `Scheme.ΓSpecIso.inv` and the fibre's
`appTop`; bijectivity gives an isomorphism in `CommRingCat`, and cancellation of
`ΓSpecIso.inv` gives the required fibre isomorphism.

The statement, visibility, docstrings, and imports are unchanged. Both planned theorem
imports are used, and the DAG proof and proof dependencies already describe this route.
No node changes are necessary. Single-file compilation passed without warnings.

Search: LeanFinder query "proper flat morphism geometrically reduced connected fibres
structure sheaf global sections isomorphism" returned flatness declarations but no direct
replacement. Loogle found `CategoryTheory.IsIso.of_isIso_comp_left`. Local `rg` found the
existing fibrewise criterion, field theorem, and the definition of
`Scheme.globalSectionsRingHom` in `WeilConjectures.AlgebraicGeometry.Cohomology.Defs`.
The source library also has `GlobalSectionsBijective.of_geometricallyConnected`; the
recorded field theorem directly fits the DAG route and was used. Import-direction checks
permit both proof imports.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.isIso_structureSheafMap_of_proper_flat_geometricallyReduced_connected_fibers`
(node `lem-sc-proper-flat-global-sections`). No `sorry` remains in the item and no new
hole was added. This is a proof from the existing stated dependencies, which themselves
still contain holes: `AlgebraicGeometry.isIso_structureSheafMap_of_proper_flat_fiberwise`
(node `lem-sc-proper-flat-global-sections-criterion`) and
`AlgebraicGeometry.Scheme.globalSectionsRingHom_bijective_iff_geometricallyConnected`
(node `lem-pc-h0-geom-connected`). Those modules were not changed.

## No longer needed

None. No imports, nodes, or modules were pruned. The existing plan is realized as stated;
its geometrically reduced/connected definition node is used through the hypotheses.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface issue found. The field theorem uses a bijective ring hom,
whereas the criterion uses an `IsIso` on `appTop`; the explicit `ΓSpecIso` composite and
isomorphism cancellation supply this glue without another statement.

## Second reading by V3

1. Compared the delivered module with the repository version. The theorem statement, declaration visibility, docstrings, and imports are unchanged; only the proof body differs.
2. Compiled the module with `lcompile.py`; it succeeds with no errors and no warnings. The proof introduces no forbidden declarations or hollow definitions. The remaining `sorryAx` comes only from the two imported dependency theorems listed above.
3. Checked the proof route and statement strength. The fibrewise criterion is applied exactly as stated; properness is obtained by pullback stability, and the global-sections field theorem is converted to the required `IsIso` using the canonical `ΓSpecIso` map and cancellation. No new statement was split off, and the theorem remains exactly as strong as the target node.
4. Checked pruning and imports. Both proof-only imports are used, all public imports support declarations in the interface, and no old proof dependency or module is unused. The unit route remains the planned criterion followed by the geometrically connected global-sections theorem.
5. Checked the DAG node against the Lean declaration. The node's proof, proof dependencies, and proof origin describe this route, and no statement or definition change requires a change record.

Changed in this second reading: added this review section only; no Lean, DAG, or import changes were needed.
