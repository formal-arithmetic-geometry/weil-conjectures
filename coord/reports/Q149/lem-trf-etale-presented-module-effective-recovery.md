# Q149: lem-trf-etale-presented-module-effective-recovery

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-etale-presented-module-effective-recovery.json`: statement node, split in eight steps; no Mathlib match for the entire assertion.
- `citations.json`: one verbatim statement quotation per node used by each step (19 records). Full statements are quoted to retain their hypotheses and all clauses used.
- `report.md`: this report. `searches.jsonl` was produced by the required search command.

No new nodes and no new Mathlib leaves. Existing search history and all imported/ancestry fields were retained. Only the assigned item is changed in the DAG. The statement and statement dependencies are unchanged.

## Attachments

None. Searched `lean/WeilConjectures/` for the item's exact blueprint tag and the notions of effective recovery, local cokernels, Zariski/etale comparison and quasi-coherent etale modules. There is no project declaration asserting all the item's clauses. Read `WeilConjectures/AlgebraicGeometry/EtaleQuasiCoherentDescent.lean`, especially its `isSheaf_etaleTensorSectionsPresheaf`: it proves the sheaf condition for extension of an already given quasi-coherent Zariski module, not recovery of an arbitrary presented etale module. The broader textual search in `lean/Sheaf/` also gave no exact attachment. No compiler was run.

## WANTED

None. The proof uses the available Stacks source.

## Findings and repairs

The item was an unsplit statement with no proof. There was no earlier sandbox attempt or released repair note to retain. Its statement is true as written. The main gaps to discharge were: arbitrary small free summands, lifting the presentation map, ensuring all overlap modules are quasi-coherent before applying full faithfulness, the cocycle verification omitted in 03DX, effectivity for a covering family without quasi-compact individual members, gluing inverses as well as forward maps, and identification of the canonical counit rather than an arbitrary final isomorphism. All are now explicit.

Read the current `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` ancestor and unit, the chapter section, and the DAG chapter/unit records. The inherited ancestry is historical: the current `lem-trf-local-term-locality` is a contracting-local-term result, while this item sits below the pre-existing section-algebra/polarized-descent specialization chain. The split retains that recorded ancestry and realizes the local-cokernel recovery input of `lem-trf-scheme-zariski-etale-quasi-coherent-equivalence`; it does not claim the current local-term proof itself states a comparison of module categories. No chapter, unit route or target was changed.

## Unfinished work

None for this one-level stage-1 split. Referenced unsplit inputs remain their own work items. No Lean or stage-2/3 work was attempted.

## Mathlib and duplicate searches

Fresh Q149 searches ran with `msearch.py`: LeanFinder with two distinct formulations, Loogle with `SheafOfModules.IsQuasicoherent, CategoryTheory.Functor.EssSurj`, LeanSearch for the Zariski/etale comparison, and a source grep for etale/quasi-coherent/descent combinations. All services returned normally. The results were read: `QuasicoherentData`, `presentationOfIsCokernelFree`, and `IsQuasicoherent` package presentations on a single ringed site and do not recover a Zariski module from a small-etale module. Read Mathlib `Algebra/Category/ModuleCat/Sheaf/Quasicoherent.lean` at the presentation-to-cokernel constructions and the quasicoherent-data predicate. Read the grep hit `AlgebraicGeometry/Morphisms/LocalFlatDescent.lean`: it concerns properties of morphisms, not the required equivalence. These are not matches for the item. Exact command queries and result names were added to `mathlib_searches` from the command's log; inherited Q106 searches remain unmodified.

Searched the full DAG for tags 03DX/023T, local cokernels, quasi-coherent coproduct/cokernel closure, module pullback, fpqc effectivity and Hom gluing, and searched the whole imported blueprint with `blueprint_refs.py search 'etale quasi-coherent'` and `search 'quasi-coherent modules'`. The latter recovers the existing fpqc descent, associated-module and quasi-coherence nodes. Reused existing statements throughout, including the sibling extension/Hom lemma. No duplicate or clause-restating node was made.

## Not duplicates

No new nodes, so there are no new/existing-node pairs to justify.

## Review by Q149

I read Stacks `descent.tex`, Tag 03DX (`proposition-equivalence-quasi-coherent`), its complete presentation/cokernel/descent/gluing proof and the final instruction to repeat it for the small etale site. I also read its preceding full-faithfulness proof, Tag 0GN7 (`lemma-fully-faithful-associated`), the fpqc descent statement Tag 023T (`proposition-fpqc-descent-quasi-coherent`), and `sites-modules.tex` Tag 03EM (`lemma-internal-hom`). There are no new-node sources to review. The proof follows that route. The final unit/counit normalization is the explicit adjunction calculation using the existing extension/Hom statement.

For step 1, I opened `lem-weil-pbc-spec-tilde-free-module`: its rank-one case explicitly states quasi-coherence of the free rank-one structure module on an affine. `pqf-def-coherent` makes this affine-local, and `lem-weil-pbc-quasi-coherent-module-coproduct-closure` covers arbitrary small coproducts, not just finite sums. I checked that `lem-trf-etale-extension-free-presentations-hom` states both colimit preservation and the image of the structure module. Thus the free-module identifications are justified without assuming finite presentations or computing infinite sums sectionwise on non-quasi-compact opens.

For step 2, the same extension/Hom node states the exact Hom bijection for quasi-coherent modules and preservation of all small colimits. Both hypotheses hold for the two modules from step 1. The cokernel closure node explicitly gives quasi-coherence of the categorical cokernel of a map between quasi-coherent modules. The given exact presentation and the preserved cokernel are compared by the cokernel universal property, which also gives compatibility with their projections. I use the statements of those nodes, not their proofs.

For step 3, `def-weil-pbc-etale-site` explicitly says fibre products exist in the small etale site and are the scheme fibre products. The pullback-quasi-coherent node supplies quasi-coherence of both overlap modules. The extension/Hom node explicitly states natural restriction identification for each etale object and compatibility with composition and module maps. Hence its Hom bijection applies on the overlap. Lifting the inverse and using faithfulness proves invertibility without assuming it of a merely lifted morphism.

For step 4, I verified the composition directions: with maps written in functional order, `(b_k^{-1}b_j)(b_j^{-1}b_i)=b_k^{-1}b_i`. The scheme-pullback definition states the canonical composition identifications; the extension/Hom node states their compatibility. The pullback-quasi-coherent node keeps the triple-product modules in the range of the Hom bijection. Faithfulness gives the cocycle. I replaced a possible implicit use of restriction compatibility along the diagonal by the simpler calculation `e_i^2=e_i` after pulling the already proved cocycle to the small diagonal; invertibility gives `e_i=1`. This avoids assuming the diagonal comparison without explanation. This is elementary cancellation from the cited statements, not a hidden lemma.

For step 5, I read the fpqc-finer-than-etale node: its conclusion is about arbitrary covering families and its finite-affine-refinement condition; it does not assume each arrow is quasi-compact. The item gives exactly a jointly surjective etale family. Clause (1) of `lem-pc-fpqc-descent` explicitly supplies effective descent for quasi-coherent modules with overlap isomorphisms and the triple cocycle. Steps 2--4 supply precisely those data. No separatedness, Noetherian, quasi-compact base or finite presentation hypothesis is used.

For step 6, I checked the descent-isomorphism orientation `a_j=phi_ij a_i` and calculated that the local maps `b_i L(a_i)` agree. The cited `lem-pur-sheaf-hom-cover-gluing` explicitly glues arbitrary compatible module maps over a covering family of a site with the needed fibre products. This applies at the terminal etale object, for the structure ring sheaf and both module sheaves. Applying it again to inverses and then its uniqueness clause proves the global map is an isomorphism and proves its uniqueness. It is not an application of a line-module-only gluing node.

For steps 7--8, the extension/Hom node supplies the adjunction and the unit normalization for every quasi-coherent Zariski module. Thus `a=R(b) eta_F` is the required restriction isomorphism; the affine-local definition transfers quasi-coherence across it. The adjunction transposition formula gives `b=epsilon_G L(a)`, so the canonical counit is invertible. Finally, applying its triangle identity at the now quasi-coherent `RG`, whose unit is identity on each open, gives the exact identity-on-opens assertion. I checked this for the named canonical counit, not a map transported without an adjunction equation.

Against delivery-errors B--E: the item is self-contained and unchanged, every proof step has a source and Boolean elementary flag, all non-elementary inputs are cited as actual nodes, and `proof_deps` is their union. Every citation was compared with its statement and copied verbatim to `citations.json`. There are no newly created statements, Mathlib leaves without declaration evidence, hidden proof sketches in unsplit nodes, duplicate nodes, relabelled item clauses or source/route substitutions. No step exceeds 2000 characters. I checked the dependency graph does not intentionally cite the parent equivalence or any result deriving recovery from it; the server check verifies acyclicity.

Edge cases checked: the zero module, empty generator or relation sets, infinite small sets, the identity cover, covers with empty members, arbitrary non-separated overlaps and the empty scheme with the empty cover. For an empty relation set the cokernel is the given free module; for an empty generator set the presented module is zero. An empty cover can cover only the empty scheme, on which the module sheaf is unique, so the descent and unique gluing arguments still apply. The diagonal normalization uses only pullback of an invertible map and cancellation. All claims remain true; no statement dispute is needed.

The off-unit nodes are generic tools declared in `split_report.tool_uses`: affine rank-one quasi-coherence, coproduct and cokernel closure, pullback preservation, conversion of etale to fpqc coverings, effective quasi-coherent descent, and module Hom gluing. They supply the exact tools called for by the 03DX proof; they do not replace a higher-level route.
