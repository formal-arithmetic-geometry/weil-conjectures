# Stage-1 worker report

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-fppf-scheme-data-sheaf-gluing.json`: statement unchanged; eight proof steps; status split; Mathlib searches retained and supplemented; blueprint same_as checked; two generic tool uses declared in split_report.
- `citations.json`: a verbatim statement quotation for every dependency cited by every numbered proof step.
- `searches.jsonl`: actual results recorded by the prescribed msearch.py command.
- `report.md`: this report and Q124's signed mathematical review.

## New nodes

None. Zero new Mathlib leaves. The prerequisite representable-sheaf assertion has a Mathlib specialization, but it is also a few-line deduction from existing DAG nodes, so it is written in step 1 rather than made a new node.

## Attachments

None. Searched WeilConjectures for the exact blueprint tag and for scheme descent, fppf, represented sheaves and gluing. The exact tag has no hit. Read EffectiveDescent.lean, Comma/Over/DescentRepresentable.lean, and the relevant descent and site source introductions. Existing scheme effectivity and descent-of-a-representing-object results assume additional effectivity/base-change inputs; they do not state this item's sheaf-valued gluing functor and natural comparison. No sorry declaration is treated as a finished proof.

## WANTED

None. All mathematical sources used are present in literature/stacks-project.

## Corrections and scope

No statement correction or STATEMENT-DISPUTED issue was necessary. The item arrived unsplit with no proof; there was no prior sandbox split to resume. The existing searches in the live item were retained. New queries and actual responses are recorded separately in searches.jsonl and in the node; the old unavailable LeanSearch response remains unavailable rather than being rewritten as a negative result.

The 02W5 source constructs the left-to-right functor by a sheaf coequalizer and omits the quasi-inverse check. This delivery follows the item's specified slice-gluing formulation: the existing 04TR/04TQ theorem supplies gluing, and the proof spells out the representation, overlap and naturality checks omitted in 02W5. It does not assume scheme descent is effective or claim that the glued sheaf is itself represented globally.

I read the current main-20261015 ancestor proof and its blueprint_update, and the unit/chapter records. The inherited ancestor association is to geometric quotient-presentation support below the local-term specialization chain; the current local-term proof itself is the contracting-correspondence argument, not a statement of this descent lemma. I preserved that provenance and the current ancestor update, and did not change any chapter or unit route. The split_report describes exactly the inherited support place this item realizes.

## Existing-node and blueprint searches

Searched the whole DAG by 02W5, 04TR, 04TQ, 023Q, gluing, representability, subcanonical/fppf and Yoneda, and searched the project Lean sources by the exact item tag and concepts. Ran blueprint_refs.py ancestor on the item and search on 'glue sheaves', '04TR', 'Yoneda', 'descent data', 'fppf', 'subcanonical', 'representable sheaf', '023Q', and 'fppf represented slice'. The Yoneda hits include the existing lem-pc-yoneda, reused here. No blueprint statement duplicates this complete functorial scheme-data gluing assertion, so same_as is empty.

Read lem-pe-set-sheaf-cover-descent and lem-pe-site-sheaf-gluing. The former states both object gluing and unique map gluing, unlike a definition of gluing or a bare existence assertion, and therefore supplies exactly steps 3 and 5. Read lem-trf-fppf-local-representations-fully-faithful but did not cite it: this proof constructs its own comparison for arbitrary R and does not need that sibling result. The parent representability/descent-data equivalence was not cited, avoiding a cycle.

## Mathlib searches and candidates

All new searches ran using msearch.py Q124 lem-trf-fppf-scheme-data-sheaf-gluing, with exact queries and responses in searches.jsonl. Two semantic phrasings of the gluing problem found Zariski scheme glueData declarations, the abstract Pseudofunctor.isEquivalence_toDescentData, and dense-subsite equivalences. Read Representability.lean lines 19–55 and IsStack.lean lines 71–78: the former needs open immersions in the Zariski topology, and the latter assumes IsStack. Neither is a one-line specialization giving this scheme-data construction and its comparison equations.

The representable-sheaf searches found Subcanonical.isSheaf_of_isRepresentable. Read Canonical.lean lines 143–156, SubcanonicalOver.lean lines 25–26 and its proof, and Fpqc.lean lines 81–98. Mathlib indeed proves the prerequisite on fppfTopology.over T by the fppf and slice Subcanonical instances. It is not a match for the whole item. Rather than create a redundant prerequisite node, step 1 derives this prerequisite directly from the existing finite affine refinement, fpqc definition and fpqc descent of scheme morphisms. This also explicitly checks that the descended map is over the required base.

## Tool uses

The split_report declares lem-pe-set-sheaf-cover-descent as the general sheaf gluing tool required by the 02W5 route, and lem-pc-fppf-affine-refinement as the general covering refinement tool needed to apply the fpqc descent leaf. Neither replaces an argument of the unit: they are tools below the fixed unit route. No top-level tool_uses field was written; the maintainer decides the recorded declarations on review. Other cross-unit results used are definitions or Mathlib leaves.

## Not duplicates

No new nodes. Reused the existing slice sheaf descent theorem, Yoneda bijection, uniqueness of representing objects, finite affine refinement, and fpqc descent of morphisms. The representable-sheaf prerequisite and fibrewise product calculations were kept as steps rather than duplicated as nodes or used to relabel clauses of the item.

## Review by Q124

I read descent.tex Tag 02W5, lemma-descent-data-sheaves, including the local representable comparison and the omitted quasi-inverse verification; sites.tex Tag 04TR, lemma-glue-sheaves, its immediately preceding gluing datum and the compatible-tuple formula; and Tag 04TQ, lemma-glue-maps, its statement and proof. For the prerequisite I read descent.tex Tag 023Q, lemma-fpqc-universal-effective-epimorphisms, and topologies.tex Tag 021P, lemma-fppf-affine, Tag 021O, lemma-fppf, and Tag 022C, lemma-zariski-etale-smooth-syntomic-fppf-fpqc. There are no new-node source statements to review. No SGA source is used.

1. Step 1 uses lem-pc-fppf-affine-refinement for an fppf covering of an affine scheme, precisely its stated hypothesis. The base-change axiom in def-weil-pbc-sites-and-cohomology gives that covering after pullback to each affine open A. An open of V_b times_V A is an open of V_b because A is open in V. The finite refinement therefore verifies exactly the finite-affine-open condition in def-weil-pbc-fpqc-covering; flatness is already in def-pc-fppf-site. Read lem-weil-pbc-fpqc-representable-descent: it glues underlying scheme maps, not automatically maps over a base. The proof supplies that extra check by its uniqueness with target B. Thus it really produces the slice sheaves needed below, without misquoting fpqc descent as a theorem with stronger wording.

2. Step 2 uses only def-trf-scheme-cover-descent-datum, def-pc-fibre-product and def-pur-localized-ringed-site. They give the actual overlap scheme maps, their cocycle, unique test maps into the fibre products, and sectionwise slice restriction. I checked the two coordinates and the direction: theta goes from F_i to F_j, by projecting phi_ij(x,a_j). Naturality is precomposition of these maps, the inverse uses phi_ij inverse, and the triple identity is the datum's own cocycle evaluated on a test object. This is elementary evaluation, not a hidden gluing theorem.

3. Step 3 cites lem-pe-set-sheaf-cover-descent. Its statement really supplies local isomorphisms e_i with e_j=phi_ij e_i, and its last sentence supplies unique morphism gluing. Its smallness, all-fibre-products, set-indexing and product-size hypotheses are provided by the fixed universes, the scheme fibre-product node and the stated site skeleton. The localized-site node identifies iterated slices sectionwise. No existence of a scheme representing the global glued sheaf is assumed. The arbitrary choices of gluing representatives are within the fixed enlarged universes.

4. Step 4 writes beta and its inverse explicitly, separating all maps W to X_i by their structure composite a:W to T_i. The slice restriction definition identifies G(D)|_{T_i}(W,a) with G(D)(W); naturality follows on the arrow (W',ag) to (W,a), not by an unproved change of base. The sheaf definition in def-weil-pbc-sites-and-cohomology makes a product of two sheaves a sheaf by gluing its two coordinates. Thus this step needs no additional theorem about products or representability.

5. Step 5 uses the morphism clause of lem-pe-set-sheaf-cover-descent, not merely its object-existence clause. I checked the conjugation identity on a double slice; the theta inverse occurs on the D' side in the right direction. Morphism gluing defines G(f), and its uniqueness proves composition and identity after restriction. The final displayed beta equation is computed using step 4. This proves the functorial clause rather than citing it from the parent equivalence.

6. Step 6 uses def-pc-fibre-product and the actual evaluation bijection in lem-pc-yoneda. The test object has both coordinates a_i and a_j, so it tests the full scheme comparison over T_i times_T T_j. The equality e_j=theta_ij e_i makes the G(D) coordinate unchanged. Yoneda therefore identifies the map with phi_ij; this does not infer a scheme equality from points over one fixed field.

7. Step 7 uses lem-pc-representable-unique for the isomorphism beta inverse alpha of represented functors, exactly what that node states, and lem-pc-yoneda for faithfulness of maps. I checked epsilon's direction Y_{D,i} to X_i so that the final natural isomorphism is RG to identity. First-coordinate preservation checks the maps are over T_i. Both overlap comparisons preserve the same three coordinates, so their represented maps agree, giving a morphism of descent data; inverting the equations gives the inverse datum morphism. This is a short assembly from existing statements, not a new lemma displaced from the item.

8. Step 8 uses lem-pc-yoneda to turn equality of represented transformations into equality of the local scheme maps; the sheaf-map equality is expanded using step 5 and R's stipulated id-times-v property. It proves naturality for every f and every i, not just isomorphisms. The definition of descent-data morphisms is cited for componentwise equality, and the gluing theorem covers the empty family case.

I tested the single identity covering: e and beta identify the original represented slice sheaf with its product representation and epsilon is precisely the chosen representing-object comparison. For repeated indices I checked the scheme cocycle is evaluated on triple slices rather than assuming phi_ii is identity on the whole double fibre product; no such false assertion occurs. Empty X_i gives empty representables except on the empty test scheme, where a represented sheaf has its required singleton section set. For the empty covering T is empty and the sheaf condition gives one section on the only empty-scheme object, so every componentwise condition is vacuous and the assertion still holds. Infinite covers use set-indexed products in the cited gluing theorem and only finite affine refinements locally; neither a global finite cover nor global quasi-compactness is assumed. No affine intersection, separation, finite-type, noetherian or scheme effectivity hypothesis has been added.

During this reading I corrected step 1 to cite the site base-change axiom explicitly, and kept the structure-map check after fpqc descent. All non-elementary inputs now occur in the uses lists, and every citation has a verbatim statement in citations.json. No proof step exceeds 2000 characters; the longer calculations are still under 1100 characters and contain no new independent lemma. The existing-node statements were opened, rather than relying on their titles or proofs. The complete statement and statement dependencies are preserved.

## Unfinished work

None in the requested one-level split. Server preflight and delivery results are recorded below after running the prescribed commands.

## Validation

The prescribed deliver.py --no-push invocation exited 0 and printed `OK (not pushed)` at commit 17fbed03a82; the Weil server preflight, including the DAG and split checks, passed. No compiler or Lake/build command was run. All worker-written files are in the assigned sandbox. The actual push is run only after this dry run exited.
