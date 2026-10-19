# Worker report: lem-coef-coherent-inner-anodyne-equivalences

## Files written

- `dag/nodes/sec-six-functors/lem-coef-coherent-inner-anodyne-equivalences.json`: repaired item split; no statement or Lean record change.
- `citations.json`: twelve verbatim statement quotations covering all uses in the seven repaired proof steps.
- `searches.jsonl`: Mathlib searches run for the item with msearch.py.
- `report.md`: this report.

No new DAG node was created. The repair cites the existing split node `lem-coef-coherent-realization-bead-normal-form`; it already states the free bead presentation, the subcomplex image criterion, and compatibility with simplicial operators. Its statement is strictly smaller than the item: it proves a normal form for coherent realization and says nothing about inner-anodyne maps, horn attachments, J-cofibrations, or Dwyer–Kan equivalences.

## Attachments

None. I searched the project source for the item id, coherent-inner-anodyne terminology, and the upstream declaration; no sorry-free declaration states the item.

## WANTED

The HTT reading copy used by the existing item is online only; an archival copy of Lurie, *Higher Topos Theory*, Lemma 2.2.5.2 and the preceding cubical proof remains wanted. The existing proof origin and WANTED source entry are retained.

## Repair of the returned split

The return identified item step 2 (2180 characters) as a non-elementary step hiding several lemmas. I preserved the item statement, source, Lean record, route, and the original horn/cube/saturation argument. I replaced the returned step 2 by one 1262-character step that cites the existing `lem-coef-coherent-realization-bead-normal-form` statement for the free flag/bead normal form, face-subcomplex image, and simplicial-operator compatibility. The resulting proof has seven steps; every step is below 2000 characters. `proof_deps` is exactly the union of the step uses and now includes that existing node. No new node restates a clause of the item, and no cycle is introduced: the existing bead-normal-form dependency closure does not reach this item.

## Not duplicates

- `lem-coef-coherent-realization-bead-normal-form` vs `lem-coef-coherent-inner-anodyne-equivalences`: the existing node gives a free bead normal form and subcomplex criterion for arbitrary coherent realizations; this item proves coherent realization of every inner-anodyne map is a Dwyer–Kan equivalence, including horn cube attachments, saturation, and J-cell equivalence.
- `lem-coef-coherent-realization-relative-cells` vs `lem-coef-coherent-inner-anodyne-equivalences`: the existing node gives a cellular presentation for degreewise injective realizations; it does not assert inner-horn lifting or Dwyer–Kan equivalence.
- `lem-coef-simplicial-interval-lifting` vs `lem-coef-coherent-inner-anodyne-equivalences`: interval-lifting states the generating J/I model structure and retract-of-cell factorization; it does not identify coherent realizations of inner-anodyne maps.

## Review by Q74

I read the authoritative item node in the shared DAG, its seven-step returned proof, the complete statement of every cited dependency, the current `sec-six-functors` chapter and `sk-prop-sf-biduality-general` unit, and the existing `lem-coef-coherent-realization-bead-normal-form` node. I also read the relevant HTT Lemma 2.2.5.2 route and the Riehl–Verity bead-normal-form source used by that existing node. The item statement remains byte-for-byte unchanged: it defines inner anodyne maps by weak saturation of inner horns and concludes that the subset-poset coherent realization is a Dwyer–Kan equivalence, with no quasicategory assumptions.

Step 1 uses the colimit formula in `lem-coef-pinched-cube-latching`; the compatible-simplex mapping calculation is explicitly written and only establishes colimit preservation and retract preservation. Step 2 now uses the exact statement of `lem-coef-coherent-realization-bead-normal-form` for the free bead presentation of the simplex, its face-subcomplex image criterion, and the simplicial operators that rewrite images as unique bead words. The subset-poset model in `lem-coef-pinched-cube-latching` supplies the flag interpretation; `def-cbc-enhanced-diagrams-cones` supplies the standard simplex/horn definitions. I checked that the replacement does not claim degreewise colimits from the bead node: it uses the node only for the normal form and subcomplex criterion, the subcomplex-image assertion directly supplies the needed realization of the union of faces, so the old inline enriched-colimit construction is no longer needed.

Step 3 still checks the exceptional mapping pair `(0,n)` of an inner horn and identifies the omitted zero-face. It uses the standard horn definition, the subset-poset cube, and the two-object `U(K)` construction in `lem-coef-simplicial-interval-lifting`. Step 4 checks the coordinate expression as a pushout-product; its monomorphism and anodyne hypotheses are supplied by `lem-coef-sset-anodyne-pushout-product` and the Kan-fibration convention in `lem-coef-kan-quillen-right-proper`. Step 5 uses exactly the local Kan-fibration clause of J-injectivity in `lem-coef-simplicial-interval-lifting`; object maps are fixed and all compositions through the newly filled `(0,n)` mapping set lie in the stated coordinate-one faces. Step 6 expands the elementary closure argument for isomorphisms, pushouts, continuous transfinite compositions, and retracts, then applies the minimality definition of inner anodyne maps. Step 7 cites the stated J-cofibrations-as-retracts-of-J-cells clause of `lem-coef-simplicial-interval-lifting` and the J-cell Dwyer–Kan equivalence/retract-closure clauses of `lem-coef-simplicial-interval-cell-stability`.

I verified the hypotheses at the edge cases: for `n=2`, the open box is the endpoint inclusion into `Delta^1`; for `n=3`, it is the indicated three-sided square; the product with no other coordinates is `Delta^0` and its boundary is empty. Identity maps, empty or zero-length attaching diagrams, arbitrary small ordinal lengths, and arrow retracts are covered by the same lifting and closure definitions. The horn argument imposes no local Kan condition on either source or target and no distinctness condition on object images. The seven dependency statements say exactly the clauses quoted in `citations.json`; no proof body of a cited node is used. I checked the dependency closure of the newly cited bead node and found no path back to this item, so the repair remains acyclic.

The preserved attempt ran Mathlib searches for the item using LeanFinder, Loogle, grep, and LeanSearch via `/home/ubuntu/weil-launcher-nt/msearch.py`; their logged queries and result summaries are retained in `searches.jsonl` and the item's `mathlib_searches`. I read those results; the statement and search question have not changed, so I did not rerun them. Hits concern ordinary nerves, quasicategories, horn generators, and inner-anodyne pushout products. None states the subset-poset coherent-realization Dwyer–Kan theorem, so the item remains a non-Mathlib statement. No SGA source is used.

Against delivery-errors B–E: TeX remains single-escaped; all cited ids exist and are unmerged; every citation quote is verbatim; every proof use is listed in `proof_deps`; the new citation is an existing node rather than a duplicate; no hypothesis was added or removed; and the only changed content is the returned long step and the mechanically dependent proof-dependency/review metadata. No compiler, Lake, build, or Lean source was run or modified, as required for stage 1.


## Resumed repair verification

The initial required dry run of the preserved work passed at `22245189c7` (not pushed). I compared the sandbox node to the current shared node: the statement, Lean record, statement dependencies, source and all six proof steps outside step 2 are unchanged. The returned 2180-character step is replaced by the 1262-character citation of the existing bead-normal-form lemma. Its three relevant assertions cover the former hidden arguments separately: the free-word clause gives unique indecomposable factorization; the injective-subcomplex clause gives the face-union image without rebuilding an enriched colimit; and the operator clause gives simplicial compatibility. Therefore no new node is needed. I checked all 208 nodes in its dependency closure for a path back to this item; none exists.

I reread HTT Lemma 2.2.5.2 online, including the exceptional mapping pair and cube pushout, and Riehl–Verity §5.1, especially Example 5.1.7, Lemma 5.1.9, Definition 5.1.11 and Proposition 5.1.12. These support the unchanged flag/horn route. There is no local archived copy of either source in the repository, and no new literature was downloaded. The WANTED archival-source entry remains applicable. I searched the entire read-only `WeilConjectures/` source for the item tag, `coherent_inner_anodyne`, inner-anodyne terminology and rigidification: only unrelated Fourier-transform rigidification hits appeared, so there is no project attachment. Whole-blueprint searches for beads and coherent realization found no duplicate statement.

I corrected the preserved report's stale count of ten steps to seven. I also replaced citation snippets that, though verbatim, selected irrelevant clauses: the pinched latching assertion was not the colimit formula or subset-poset definition used here; the Kan-complex fibrant-object sentence was not the Kan-fibration lifting definition; and the J-injectivity clause was not the retract-of-cell assertion used in step 7. Each citation now quotes the actual contiguous statement passage supplying that step's input. The bead quote includes all three clauses used in step 2. All seven proof steps are under 2000 characters, and no statement or Lean record changed during this resumed repair.
