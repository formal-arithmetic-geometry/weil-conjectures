# Worker report — Q78

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-a1-finite-affine-family-fppf-algebra.json`: statement item, now split into seven steps; the statement and statement dependencies are unchanged. The full statement is not a Mathlib leaf; its ingredients are existing Mathlib leaves.
- `citations.json`: fifteen entries, one for each citation in each proof step, quoting the cited statement verbatim.
- `report.md`: this report. No new nodes, hence zero new Mathlib leaves.

## Attachments

None. Searched the live `lean/WeilConjectures/` for the exact blueprint tag and id, finite affine families, sigmaSpec, and faithful-flat product constructions. The sigmaSpec structure lemma in `Mathlib/AlgebraicGeometry/Limits.lean` under WeilConjectures concerns a family of copies of one ring, not this item; other spectrum-product uses concern normalization or Galois decompositions. No project declaration found states all the item's clauses.

## WANTED

None. All source material used is available locally.

## Corrections and observations

The item was unsplit and had no earlier sandbox node or report. No repair note exists for it. I preserved its full statement, source, blueprint ancestry, prior searches, and other original fields, and added the actual Q78 search records. The statement is true; no STATEMENT-DISPUTED correction is needed.

The source is the finite-disjoint-affine replacement in Stacks descent.tex Tag 02KL, `lemma-flat-finitely-presented-permanence`, locally-of-finite-type alternative. The source abbreviates precisely this assembly, which is now expanded. The inherited source place mentions Tag 00HP; the applicable existing criterion is the ring formulation Tag 00HQ, `lemma-ff-rings`. The proof cites that exact node rather than claiming the module definition proves faithful flatness.

The latest blueprint is main-20261024, ef6f9619fdbffa59e88528fb56483d76c70258c8. I read the current `lem-a1-affine-hc0.md` and its proof under `literature/blueprint/latest/`. That ancestor now proves compactly supported degree-zero vanishing via finite coefficients, and does not contain a literal finite-affine-replacement sentence. The item is a generic auxiliary theorem on the recorded historical ancestry through source descent, not a replacement of the current cohomological proof. This distinction is made explicit in split_report.blueprint. The chapter and unit records were read and left unchanged.

## Searches and reuse

DAG searches included finite products and coproducts, flatness, affine finite type and finite presentation, faithfully flat surjective spectra, and source tags. Blueprint-wide searches with `tools/blueprint_refs.py search` included `finite product`, `coproduct of affine`, `flat finitely presented`, and `faithfully flat`; no imported blueprint node states the whole item. The ancestor command returned lem-a1-affine-hc0. I found the existing finite-affine-coproduct, finite-product-flat, single-affine-flat, pointwise lft, all-affine-pairs lft, affine-open lfp, surjective-spectrum faithful-flat, and universal-injectivity leaves and reused them. In particular, the all-affine-pairs flatness criterion alone does not immediately prove flatness from one affine pair; the proof uses `lem-weil-pbc-flat-ring-map-iff-flat-affine` instead.

All new Mathlib searches were executed using msearch.py and read, including a second semantic phrasing. LeanSearch and the first LeanFinder returned sigmaSpec, finite-isomorphism, finite-product finite-presentation, and flat-surjective faithful-flat declarations; Loogle returned Flat.SpecMap_iff and the faithful-flat criterion. The second semantic phrasing returned only affine-cover/limit infrastructure. Source read: Mathlib AlgebraicGeometry/Limits.lean:604-647 and Morphisms/Flat.lean:50-68, plus the statement and match records of every reused node. These give the ingredients, not all constructions and clauses in one specialization. No new node is justified or needed.

## Not duplicates

No new nodes were created. The potentially overlapping reviewed `lem-trf-finite-affine-composite-presentation` has a locally finitely presented composite hypothesis, whereas here the R-composites are only finite type; it cannot replace this item. Its coproduct and affine-criterion ingredients already exist separately and are reused directly. No statement-only node restates a clause of the item.

## Review by Q78

I read Stacks descent.tex Tag 02KL (`lemma-flat-finitely-presented-permanence`) and its proof, algebra.tex Tags 00HP (`lemma-ff`), 00HQ (`lemma-ff-rings`) and 05CK (`lemma-faithfully-flat-universally-injective`), and morphisms.tex Tags 01TP (`definition-finite-presentation`), 01TQ (`lemma-locally-finite-presentation-characterize`), 01T1 (`definition-finite-type`), 01T2 (`lemma-locally-finite-type-characterize`), and 01U5 (`lemma-flat-characterize`). I also read the finite coproduct Mathlib construction and the source text and match for the single-affine flatness equivalence. There are no new node statements whose sources need separate review.

Step 1 cites the scheme-coproduct-family statement for existence, uniqueness, and the actual coprojections, the finite-affine-coproduct-spectrum statement for the isomorphism and its restriction to every component, and def-weil-affine-spectrum for contravariant functoriality. These statements give exactly what is used. The equations with each product projection prove both structure-map identifications and the composition relation; no unspecified transport is used. Neither flatness nor finite presentation is needed here, only finiteness for the spectrum-product isomorphism.

Step 2 cites finite-product-flat-modules, whose statement includes n=0. A finite enumeration of I is only reindexing the same module. The definition of a flat ring map turns the flat product module into flatness of beta. The single-affine equivalence, unlike the all-pairs flatness lemma, actually permits this one ring map to prove the scheme map flat. The stalkwise flat-morphism definition makes invariance under the source isomorphism explicit: the relevant local maps differ by a ring isomorphism, so their tensor injectivity condition is unchanged. This is not an appeal to an unstated localization theorem.

Step 3 explicitly constructs a preimage of each y from joint surjectivity, first in Z and then in Spec B using e. It then cites exactly the flat-surjective-spectrum-faithfully-flat statement, with Step 2 supplying flatness and the constructed preimages supplying surjectivity. No finite-type condition over R is used for faithful flatness. The zero-target case poses no additional hypothesis.

Step 4 uses only the open-cover clause of the scheme coproduct and the pointwise lfp definition. For every point its own component and the whole affine target are the witnesses; the ring map is beta_i from Step 1, with finite presentation supplied by the item's hypothesis. This step is marked elementary because it literally supplies the defining witnesses; it does not use the definition for a finiteness theorem.

Step 5 uses the actual conclusion of the affine-open-lfp lemma: local finite presentation gives a finitely presented induced map on any affine pair. Step 4 gives its hypothesis; e identifies all of Z as an affine source, the target is affine, and Step 1 identifies the resulting ring map with beta. This is not an inference that a merely locally finitely presented arbitrary scheme map is globally finitely presented: only the coordinate ring map on the specified whole affine pair is asserted.

Step 6 uses the coproduct's open components, then the pointwise finite-type criterion with gamma_i. The hypothesis is exactly that R to B_i is finite type; nothing assumes these composites finitely presented. The all-affine-pairs finite-type criterion then applies to all of Z and Spec R, giving the finite-type algebra gamma. Both cited criteria were read in full and state these two directions. This avoids silently using a finite-product finite-type theorem absent from the citation list.

Step 7 uses the universal-injectivity statement with the faithfully flat A to 0 already proved in Step 3 and N=A. Its conclusion is exactly the injection used. The tensor target is zero by the pure-tensor relation, so A=0. Thus no unstated existence-of-maximal-ideals theorem is needed. The explicit R/(1) presentation checks finite type and finite presentation at zero.

Against B1-B10: no new nodes, no omitted data or notions, no doubled TeX escapes introduced, exact tags and labels recorded on steps, and actual search queries retained with their returned log records. Against C1-C8: every non-elementary ingredient is an existing cited node, each was opened and its statement quoted in citations.json, no step uses a cited proof instead of a statement, and no off-unit non-leaf is used. No new dependency points back to the item; the delivery checks must confirm global acyclicity. Against D1-D5: the proof carries the assembly, no content is moved to a relabelled node, and the source's abbreviated replacement has been expanded into the explicit maps and witnesses. Against E1-E7: I checked each finiteness and flatness hypothesis at its use, did not assume affineness of intersections, and displayed the coordinate equations rather than claiming compatibility without proof. There is no source error requiring a changed statement.

Small cases checked: the empty family (A=B=0 under joint surjectivity), A=0 (every unital A-algebra is zero), zero factors (empty components), one factor (the given map), and repeated factors (unchanged joint-surjectivity argument). The finite hypothesis is used for affineness of the coproduct and flatness of the product; no statement is extended to infinite products. Every proof step is under 2000 characters (maximum 967), so no long step conceals a comparison lemma. No SGA source, Lean edit, compiler, Lake invocation, or sub-agent was used.

## Unfinished work

None in this one-level split. The required dry run and direct delivery are performed after this report is written; their outcomes are recorded by the delivery tool.
