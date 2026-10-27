# Stage 1 delivery: lem-sfb-virtual-rank-one-cofactor-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-virtual-rank-one-cofactor-descent.json — statement, split into five proof steps, no Mathlib match.
- citations.json — 19 verbatim statement excerpts, one for every step/node citation.
- report.md — this report.

No new nodes; zero Mathlib leaves. searches.jsonl is the search command's own log. write_split.py is sandbox-only preparation, not a delivered node. The original statement, statement dependencies, source and inherited provenance are retained.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id, cofactor and Cofactor. The only cofactor occurrence is a comment about square-matrix minors in Mathlib/LinearAlgebra/Matrix/Determinant/Basic.lean; no project declaration supplies this item. Sheaf declarations are reference material, not an attachment claim.

## WANTED

None. All sources used were available locally.

## Problems found and changes

The item was unsplit and its sandbox had no node, proof or report. I copied the live item and retained its existing searches and source material. Its six earlier Mathlib searches are preserved; five fresh searches were run through msearch.py and their actual log records appended. Both semantic phrasings were read. Hits about presentations of cokernels, group cohomology, exterior-power maps and determinants of endomorphisms do not state this scheme-derived cofactor assertion. I read the candidate signatures and the local Mathlib definitions relationsOfIsCokernelFree/presentationOfIsCokernelFree (Quasicoherent.lean:92,114) and det_toMatrix_eq_det_toMatrix (Determinant.lean:119). No candidate is a one-line specialization giving the item.

The statement is not disputed. Stacks 0E9Y assumes an injective differential; its displayed formula is the source of the construction, but its theorem is not applied to arbitrary differentials here. The existing lem-sfb-cofactor-local-descent and lem-sfb-two-term-cofactor-naturality explicitly remove that hypothesis, and are the actual inputs. This avoids adding injectivity to the item silently.

blueprint_refs.py ancestor prints from.node = None for the item and its parent. This null provenance is already in the live chain; I retained it rather than invent an imported ancestor. from.place is specific, and same_as remains [] after searching the whole imported blueprint for cofactor, determinant and sheaf hom. I read the latest sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md. The latest proof (3) is a direct-image/compactification route rather than the older alteration wording preserved in this chain. This split only supplies the recorded lci-curve cofactor prerequisite and changes no chapter/unit route or record.

## Not duplicates

No new node was created, hence there are no new/existing tag pairs. Existing algebraic cofactor naturality, local cofactor descent, affine derived equivalence and general sheaf-morphism gluing are reused. The nearby lem-sc-determinant-wedge-morphism-glue is not substituted for a comparison theorem: its statement does not supply the present derived comparisons or introduce self-contained hypotheses. No imported blueprint node states the item.

## Review by ND

I read delivery-errors B–E in full and checked the actual node statements, not their proof bodies, for every citation. I read Stacks duality.tex lemma-determinant (0E9Y), more-algebra.tex lemma-determinant-two-term-complexes (0FJM) and its good-diagram proof, perfect.tex lemma-affine-compare-bounded (06Z0), and sites-modules.tex lemma-internal-hom (03EM), together with sites.tex lemma-glue-maps (04TQ). These sources give the local formula, determinant comparison, affine derived interpretation and sheaf gluing respectively. The full assertion is explicitly marked as an agent assembly. There are no new-node sources to audit and no SGA source is used.

Step 1 uses the finite-local-freeness definition to choose free affine charts, the affine tilde adjunction's colimit clause to identify cokernels, and cofactor-local-descent's basis/lift independence and localization formula to compare the local maps. I checked that its hypotheses are precisely finite projectives of ranks c,c+1; free chart modules satisfy them without any injectivity. The sheaf exterior-power definition sends restrictions to restrictions of the same wedge, so the module formula really becomes the specified sheaf formula. The gluing node is about module morphisms and not just objects; it supplies both the construction and uniqueness on arbitrary chart intersections. It is used on the Zariski open site, where its required fibre products are intersections.

Step 2 is the point where merely citing algebraic naturality would leave a gap. I use the affine derived equivalence, whose statement explicitly says termwise tilde induces the equivalence into D_QCoh; this is a full subcategory of D(O). Both models have quasi-coherent terms and hence represent objects of that subcategory. Thus their specified derived isomorphism has a preimage in D(A). The determinant statement supplies canonical model comparisons and restriction compatibility, and the item's stipulated kernel-first normalization is precisely that of algebraic cofactor naturality. I read that lemma's whole statement: it permits different c,c', noninjective differentials and arbitrary commutative rings. Exact open restriction commutes with cohomology because kernels and cokernels of the restricted complex are preserved. The equality then descends by sheaf-morphism uniqueness. Only affines inside the overlap are used, never affineness of the overlap itself.

Step 3 writes out the conjugation phi_i = d_i w_i h_i^{-1}. The preceding overlap equation gives agreement with exactly these source identifications; no comparison is assumed for free. The cited gluing theorem provides the unique linear map. The elementary label refers to substitution and one direct application of the quoted gluing statement, not an uncited descent theorem.

Step 4 reuses step 2 on the extra model against each old chart, and on the two models linked by mu^{-1} b lambda. The cited algebraic naturality gives the square, determinant functoriality supplies its outer comparison, and the written cancellation proves the claimed naturality of w_L. This is a consequence of established comparisons, not a new node restating the item's clauses. Sheaf uniqueness proves cover/refinement independence and equality globally.

Step 5 uses exact open restriction and the determinant statement's restriction/pullback comparison. For a scheme isomorphism, scalar extension on each free chart is an exact equivalence; its inverse is scalar extension along the inverse ring isomorphism. Thus it preserves cokernels and cohomology without a separate flat-base-change theorem. I checked the projective exterior-scalar comparison statement: it gives the actual pure-wedge map, the dual evaluation map, evaluation compatibility and scalar-extension composition. In particular the pulled-back dual basis is the correct dual basis, not an arbitrary line trivialization. The displayed formula is consequently the required local cofactor formula, and sheaf uniqueness proves transport. These are generic tools declared in split_report.tool_uses; none replaces a unit route.

I checked edge cases: c=0 gives the empty wedge and the canonical Q to wedge^1 Q map. A zero differential with c>0 gives the zero cofactor map, so no step asserts w is invertible. Over a nonreduced ring such as k[epsilon]/epsilon^2 the same formula and cited algebraic input apply, without any division or generic-rank argument. Adding a contractible identity summand changes c and is covered by the algebraic derived comparison, including its kernel-first sign normalization. Arbitrary overlaps are covered by smaller free affine charts; this works on nonseparated schemes and imposes no quasi-compactness. Empty opens, the empty scheme and the zero ring impose no extra condition. Every proof step is below 2000 characters, and there is no long hidden lemma moved into a new child. Every node in uses is present, its quoted substring was checked literally, and proof_deps is the union of uses.

## Unfinished work

No mathematical clause remains unaddressed at this one-level split. The cited lower nodes retain their own existing stage statuses. No Lean was written or compiled. The first dry run rejected two cofactor-naturality excerpts as shorter than its 40-character minimum. I expanded both to the full formula sentence, including the cohomology/cokernel identifications. No proof citation or statement changed. Required final dry run and push results follow from the delivery tool.
