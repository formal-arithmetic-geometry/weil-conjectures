## What changed

`picard_residue_homology_source_residue_comparison` is proved by composing the quotient-model and source-model additive equivalences. `picard_residue_homology_chosen_geometric_maps` is proved by applying the common geometric derived-fibre naturality theorem, applying the natural affine residue-model comparison, and choosing chain representatives with `perfect_affine_map_representative`. The affine naturality proof and its completed lower-level affine comparison modules are included in this delivery. Removed imports used only by the former unfinished direct construction: `AffineKFlatResiduePullbackModel`, `Mathlib.Algebra.Homology.ShortComplex.ModuleCat`, `WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat`, `PicardResidueHomologySourceFibreComparison`, `LocalizedStrictPerfectResidueHomology`, `RelativeMVMaps`, `Picard.CanonicalSinglePullbackComparison`, and `TensorPullbackAdjunction`.

## Proved and sorry left

All declarations in the delivered Lean files are proved; no `sorry` remains. The item declarations proved are `picard_residue_homology_source_residue_comparison` and `picard_residue_homology_chosen_geometric_maps`. The affine comparison chain is also proved: `affine_residue_quotient_homology_naturality`, `affine_residue_evaluation_homology_naturality`, `affine_perfect_sections_counit`, `affine_perfect_residue_model_naturality`, `derived_fiber_open_factorization`, `residueTildeHomologyComparison`, and `affine_residue_model_naturality`.

## No longer needed

The direct bypass construction and its helper lemmas are no longer needed. The removed modules listed above and their associated proof dependencies are pruned from this item's route. The completed route uses the affine naturality chain, `new-picard-derived-fibre-naturality`, and `lem-pc-perfect-affine-map-representative`.

## Where the brief, the DAG or earlier work was wrong

The DAG's planned direct construction of coefficient arrows and simultaneous residue compatibility was longer than necessary. The existing geometric derived-fibre naturality theorem supplies the common source and target cohomology comparisons; the affine naturality chain supplies the residue-model comparison and its functoriality. This avoids the former low-level direct-image bypass route.

## New nodes

This delivery restores and proves the following completed affine comparison nodes used by the route: `new-affine-residue-quotient-homology-naturality`, `new-affine-residue-evaluation-homology-naturality`, `new-affine-perfect-sections-counit`, `new-affine-perfect-residue-model-naturality`, `new-derived-fiber-open-factorization`, `new-residue-tilde-homology-comparison`, and `new-affine-residue-model-naturality`. Each node's Lean record points to its corresponding module under `lean/Sheaf/AlgebraicGeometry/`.

## Earlier second reading (a previous round; superseded)

The delivered declarations compile with unchanged signatures, and the affine naturality chain is used only through its stated interfaces. The chosen-geometric-maps proof keeps one source comparison for the whole finite family and selects chain representatives only after the derived arrows are fixed. The seven added nodes correspond to the completed helper modules and contain no additional holes.

## Second reading by M2

1. **Signatures and scope.** Compared the item module with the repository version. The theorem signatures of `picard_residue_homology_source_residue_comparison` and `picard_residue_homology_chosen_geometric_maps` are unchanged; only proofs and proof-only imports changed. The added helper modules introduce the split-off statements listed in `## New nodes`.

2. **Proof validity.** Compiled all nine delivered modules with `python3 /home/ubuntu/weil-launcher/lcompile.py --all ...`. The compile completed without errors or warnings. Searched the delivered Lean files for `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, and `extern`; none occur. The proofs use only the permitted kernel axioms through the imported library.

3. **Statements and nodes.** Read each added node and its corresponding declaration. The helper statements are strictly intermediate naturality/comparison results used by the item proof, carry source and proof descriptions, and have matching Lean records. The existing item and chosen-geometric-maps statements remain exactly as written; no hypothesis or conclusion was weakened.

4. **Pruning and route.** The item proof follows the existing source-model and quotient-model route, then uses the affine naturality chain, `picard_derived_fibre_naturality`, and `perfect_affine_map_representative`. Imports used only by the abandoned direct construction were removed and are recorded under `## No longer needed`. The unit `sk-prop-av-cube` and its realized route are retained.

5. **DAG agreement.** Checked the delivered node proof dependencies against the imports and theorem applications in the Lean files. The target node records the two model theorems used by the source-residue comparison; the chosen-geometric-maps node records the affine naturality, derived-fibre naturality, and perfect representative route. The seven added helper nodes correspond to the seven new helper modules and no unlisted holes remain.

**Changes made during second reading.** Added this second-reading record only; no Lean declarations or node statements were changed.
