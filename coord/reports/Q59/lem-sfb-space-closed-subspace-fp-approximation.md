## Worker report

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-space-closed-subspace-fp-approximation.json`: statement; split into six steps using existing nodes, with no Mathlib match for the item.
- `citations.json`: verbatim statement excerpts for every proof-step citation.
- `report.md`: this report. Search outputs and the script used to write the sandbox JSON are supporting scratch files, not delivered DAG files.

Attachments: none. The exact blueprint tag has no declaration under `lean/WeilConjectures/`. Searches by closed-subspace, algebraic-space and finite-presentation terminology found the scheme-only approximation in `WeilConjectures/AlgebraicGeometry/Morphisms/Integral/FinitePresentationApproximation.lean`, not a theorem covering this algebraic-space statement. Its scheme approximation cannot attach this item.

WANTED: none. Every source used is present locally.

The item had an empty proof and no proof dependencies. Its mathematical statement is correct and is unchanged. The missing argument is supplied by existing nodes: `lem-sfb-space-module-fp-directed-approximation`, `lem-sfb-space-qcoh-kernels-colimits`, `lem-sfb-space-qcoh-affine-chart-calculus`, `lem-sfb-space-ideal-closed-subspace-correspondence`, and `lem-sfb-space-closed-structure-finite-presentation`. The finite-type subideal index, the transition maps and the universal property are written in the steps, not moved into new nodes. The finite-type image and sum assertions are immediate finite-generator calculations using the cited chart calculus.

Unfinished work: none for this one-level split. Its cited unsplit nodes remain their own items. No Lean was written or compiled.

## New nodes

None: 0 new nodes, 0 new Mathlib leaves.

## Searches and reuse

I searched the whole DAG by the item's ID, by Tags 0A0U, 0829, 03MB and 084Q, and by finite-type submodule, quasi-coherent ideal and closed-subspace terminology. Whole-blueprint searches with `tools/blueprint_refs.py search` used `closed subspace`, `closed limit`, `closed finite presentation`, `finite type quasi-coherent`, `03MB`, and `084Q`. The first three and the last two returned no blueprint match. The finite-type query returned scheme statements, notably `lemma-nagata-ideal-directed-union-finite-type` and the scheme closed-subscheme-system definition; neither covers arbitrary algebraic spaces. The Noetherian-space coherent-union node was read and rejected because this item has no Noetherian hypothesis. I reused the existing finite-presentation module approximation and its chart calculus instead of creating a second algebraic-space union lemma.

I ran msearch.py for the item with two LeanFinder phrasings, Loogle, grep, and LeanSearch. All five searches ran successfully; the complete outputs are saved as `search-0.txt` through `search-4.txt` and the exact queries are in the node and searches.jsonl. LeanFinder found scheme limits and scheme ideal-sheaf data; LeanSearch found scheme closed-immersion facts. Loogle and grep found no match. I read Mathlib's `AlgebraicGeometry/Morphisms/ClosedImmersion.lean` (the class has `X Y : Scheme`) and `AlgebraicGeometry/AffineTransitionLimit.lean` (the diagram is valued in `Scheme`), and checked `IdealSheaf/Basic.lean` (the ideal-sheaf data is indexed by a scheme). These do not specialize in one line to algebraic spaces. Historical searches on the existing item are retained; the five new searches have this sandbox's actual logs.

## Source error

Stacks Tag 0A0U, `spaces-limits.tex`, `lemma-closed-is-limit-closed-and-finite-presentation`, says in its proof to take the closed subspace of **X** cut out by the finite-type subideals. The intended ambient space is **Y**, where these ideal sheaves live. Read literally after pullback to X, all of them are zero. For example let A be the polynomial ring over a field in infinitely many variables, let I be the ideal of all the variables, and let X=Spec(A/I) inside Y=Spec(A). Cutting the restrictions out inside X always returns X, whose immersion into Y is not finitely presented because I is not finitely generated. The intended stages V(I_a) inside Y are finitely presented. The source's theorem and this item's statement are correct; only this ambient-space typo in the proof is corrected. No statement correction is being made.

## Blueprint and route

I read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` section and direct-images proof. This item is the inherited closed-subspace approximation input to the proper-space finite-presentation system (Tag 0A0W), itself below proof (3) of the direct-images node. The split keeps that route and all non-definition proof inputs have the item's unit `sk-thm-sf-ctf-stability`. It does not use an SGA source.

`tools/blueprint_refs.py ancestor` currently returns None for this item's inherited created.item chain; the live blueprint.from.node is already null. I retained that metadata, its detailed from.place, and its via chain, and recorded the current blueprint proof place in split_report. The item is not the unit's key node, so no unit or chapter file is changed.

## Not duplicates

No new nodes. In particular the existing ideal correspondence and finite-presentation criterion are cited instead of duplicated, and no scheme-only approximation is treated as an algebraic-space theorem.

## Review by Q59

I read the statement and proof of Stacks Tag 0A0U in `spaces-limits.tex`, its explicit input Tag 0829 (`lemma-directed-colimit-finite-type`), and Tag 07V9 (`lemma-colimit-finitely-presented`). The item's hypotheses match: Y is qcqs, i is closed, and there is no Noetherian hypothesis. The source's finite-type subideal construction gives exactly the stated closed stages and closed cone, with the ambient-space correction discussed above. I also read Tag 03MB (`spaces-morphisms.tex`, `lemma-closed-immersion-ideals`), Tag 084Q (`lemma-closed-immersion-finite-presentation`), and Tags 03LZ, 03M0 and 03M1 in `spaces-properties.tex` for the module calculations used below. There are no new node statements to compare against sources.

1. Step 1 uses the actual statements of `def-a1-space-point-topology` and `def-weil-pbc-quasi-compact-scheme`: etale-chart inverse images of opens are open, and a qc scheme has the finite-subcover property. Pulling back a cover and using the atlas's surjectivity proves the needed topological qc hypothesis. The absolute diagonal hypothesis agrees with the item's base Spec Z, so no change of relative diagonal is hidden.
2. Step 2 uses `lem-sfb-space-ideal-closed-subspace-correspondence` for the quasi-coherent kernel ideal and its recovery of X, and `lem-sfb-space-module-fp-directed-approximation` for a small filtered finite-presentation-module diagram. I opened both statements. Crucially the latter says colimit in **all module sheaves**, not just in QCoh. This is exactly what step 6 needs for an arbitrary direct-image target. Its qc hypothesis was checked in step 1; its quasi-separatedness hypothesis is given.
3. Step 3 uses `lem-sfb-space-qcoh-kernels-colimits` for quasi-coherence of direct sums and images, and `lem-sfb-space-qcoh-affine-chart-calculus` for computing images on affine etale charts and testing finite type there. Those statements explicitly provide these operations, so this is not an inference from a definition of quasi-coherence. Finite presentation gives a finite generating list, its image is generated by the image list, and a sum is generated by concatenating two lists. This proves the required finite-type claims without a new lemma. The site/size convention was opened: submodules on the chosen small site form a set in the larger universe because they are families of subsets of sets of sections. Zero proves nonemptiness, and sums give an upper bound even if Y or I is zero.
4. Step 4 uses the ideal correspondence to construct V(I_a) as an algebraic space and to identify its defining ideal. The statement of `lem-sfb-space-closed-structure-finite-presentation` explicitly equates finite presentation of a closed immersion with finite type of this ideal, with no Noetherian, qc or separation restriction on the ambient space. Thus this proves full finite presentation, not merely finite type or finite presentation of some unrelated module.
5. Step 5 uses the factorization and base-change clauses of the ideal correspondence, the algebraic-space fibre-product statement, and the representable scheme-test definition of a closed immersion. For I_a contained in I_b, a map killing I_b kills I_a; this proves X_b times_Y X_a = X_b on tests. The projection is therefore the pullback of i_b, and every scheme test is a closed immersion directly by the definition. The identical argument handles X into X_a. Uniqueness inside the specified subfunctors proves all composition and cone equalities. There is no unsupported inference from containment of topological images.
6. Step 6 uses the precise direct-image factorization criterion in the correspondence node, including its validity for arbitrary algebraic-space sources, together with the all-module-sheaf colimit assertion from the module approximation. Every u_j factors through its finite-type image from step 3. Consequently the canonical map I to h_*O_T has zero composite with every u_j, and the colimit's uniqueness clause forces it to be zero. This is a complete test-object proof of the limit universal property. It neither requires preservation of kernels by pullback nor assumes the existence of an inverse limit algebraic space in advance.

I checked C1/C4 against each opened dependency statement and wrote matching verbatim citations. I checked B1--B9: no new node carries an unproved proof sketch, an undefined new notion, or a duplicate, and the item's statement remains self-contained with its original statement dependencies and TeX. D1/D2 are avoided because no clause is repackaged as a lemma: the index, inclusions and limit argument are in the item's proof. For E I checked Y empty, X=Y (I=0), X empty (I=O_Y), and a non-finitely-generated ideal on an affine non-Noetherian base. The zero ideal index makes the system nonempty in all cases, and for I=O_Y the unit ideal itself gives the empty stage. The arbitrary-source factorization criterion avoids confusing a vanishing ideal pullback with an injective pullback. All six steps are shorter than 2000 characters. The source typo was corrected in step 4; no other mathematical defect or statement dispute was found.

## Validation

The required deliver.py dry run and push are recorded by the delivery tool after this report is written.
