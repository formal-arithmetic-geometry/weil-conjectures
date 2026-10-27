# Stage-1 report: lem-sfb-scheme-quasi-affine-fpqc-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-quasi-affine-fpqc-descent.json: item, split in five steps. Mathlib search verdict: no exact match or one-line specialization.
- citations.json: one verbatim statement quotation for every node cited in every proof step.
- searches.jsonl: actual results of the required search command, retained in the sandbox.

No new nodes, no Mathlib leaves added, no Lean files written or compiled. The item statement and its statement dependencies are unchanged. No unit or chapter record changed.

## Attachments

None. Searches under lean/WeilConjectures for the exact blueprint id and quasi-affine descent found EtaleTopologicalInvariance/Descent.lean, especially Scheme.Hom.exists_isQuasiAffine_etale_obj_iso_of_etale_cover at line 777. That theorem assumes an etale cover, universal homeomorphism, and etale input, and constructs a descended object. It does not state arbitrary fpqc descent of the quasi-affine property. It is not an attachment.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Problems in the imported material and changes

The item had no proof. Its statement agrees with the descent implication of Stacks Tag 02L7, including quasi-compactness in the quasi-affine convention and the absence of finiteness and separation assumptions. I supplied the proof by the same canonical-affinization route, on each affine target chart. This lets the proof cite the already available affine-form qc/separated descent and flat-global-sections base-change nodes, without incorrectly treating them as family-form or general relative-spectrum statements.

I read the current latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, as well as the DAG chapter and unit records. The supplied blueprint ancestry has null from.node with a long recorded supporting-input chain; tools/blueprint_refs.py ancestor confirms None. I retain that metadata and describe the supporting Tag 02L7 input in split_report.blueprint. No imported ancestor or route has been rewritten.

The required searches were made through msearch.py with leanfinder, loogle, grep and leansearch, using a second phrasing and a broader IsQuasiAffine query. All returned successfully. I read Mathlib/AlgebraicGeometry/QuasiAffine.lean and Morphisms/Descent.lean: the former supplies absolute quasi-affine embedding facts, already represented by an existing leaf; the latter supplies generic descent reduction interfaces whose hypotheses still require this argument. Neither makes the item a leaf. Existing historical item searches are preserved; the new command results are appended exactly as logged.

## Unfinished

Nothing in the stage-1 split. The reused unsplit or split dependencies retain their own independent proof tasks; this delivery does not claim to finish them.

## Not duplicates

No new nodes were created. Whole-DAG tag and keyword searches and blueprint_refs.py search quasi-affine located the existing canonical embedding, affine coproduct, flat global-sections base change, qc/separated descent and open-immersion descent nodes. I reused these rather than creating duplicate relative-affinization or descent nodes. The existing space-quasi-affine-affine-descent item uses this scheme theorem and was not used backwards.

## Review by Q42

I read Stacks descent.tex, lemma-descending-property-quasi-affine, Tag 02L7, and its cited quasi-compactness (02KQ), separatedness (02KU), and open-immersion (02L3) proofs. I also read coherent.tex lemma-flat-base-change-cohomology (02KH), properties.tex lemma-quasi-affine (01P9), morphisms.tex lemma-characterize-quasi-affine (01SM), constructions.tex lemma-canonical-morphism (01LY), and schemes.tex lemma-disjoint-union-affines (01I5). These sources justify exactly the affine-chart form used here; no SGA source is used.

Step 1 uses the fpqc-covering axioms for base change and the covering definition for a finite affine refinement over a fixed affine V. I checked that the definition really provides finitely many affine source opens whose images cover V. The coproduct statement supplies disjoint open components and its mapping property, affine-morphism permanence clause (4) supplies finite-union affineness, and the affine-to-affine morphism and permanence statements supply quasi-compactness of g. The flat definition is pointwise on local rings, so restriction to opens and disjoint union preserve flatness directly. This does not infer quasi-compactness of a general member of the original fpqc family. The empty refinement forces V and its inverse image empty and is handled explicitly.

Step 2 uses the quasi-affine base-change node, whose statement allows an arbitrary base map, for each B_j to the corresponding original U_i. The target B_j is affine, so the quasi-affine definition gives the needed absolute quasi-affine W_j. The canonical-embedding node explicitly gives an open immersion and qc/separatedness; no assertion is borrowed from its proof. Disjoint target components allow those embeddings to assemble directly into an open immersion, and finite unions of qc spaces are qc by restricting an arbitrary open cover and taking the union of finite subcovers. This is an elementary coproduct assembly, not a missing descent lemma. Affineness of the finite target coproduct is exactly permanence clause (4). Separated cancellation clause (b) applies to the absolute separated W to get W to B separated. The qcqs permanence statement needs a quasi-separated target; the affine-qcqs node verifies it for B. In particular no arbitrary quasi-compact open of a quasi-affine scheme has silently been assumed affine.

Step 3 cites the two singleton descent statements only after constructing a flat surjective quasi-compact B to V. Their actual statements require all three hypotheses, which step 1 provides, and give qc and separatedness of X to V separately. The separated-implies-quasi-separated node and qcqs permanence then give absolute qcqs for X because V is affine. This is the qcqs hypothesis of the flat-base-change leaf; neither properness nor Noetherianity nor finite presentation is used.

Step 4 uses the affine-global-sections flat-base-change leaf exactly as stated: affine V and B, flat B to V, and absolute qcqs X. Its statement supplies an isomorphism of rings with formula c tensor b mapping to the product of the two pullbacks. I wrote that formula and compared it on both factors to the section map of the pulled-back canonical morphism. The fibre-product-of-affine-spectra statement identifies the correct target, and the morphism-into-affine bijection identifies the morphism from its ring map. Thus the base change is the canonical map for W under the specified spectrum isomorphism, rather than merely an unspecified identification. The canonical affine embedding node then provides an open immersion since W was already shown quasi-affine.

Step 5 uses flat and surjective base change to check the covering of D, not merely the covering of V. D and D times_V B are affine by the affine-spectrum fibre-product formula of step 4. The affine open-immersion descent leaf therefore has precisely its required hypotheses. Its conclusion gives an open immersion X into D. The image is qc because it is homeomorphic to qc X; this gives a qc open subscheme of an affine scheme, exactly the conclusion in the item's convention. Repeating for every affine V proves the original morphism condition.

I tested the empty target, empty source, one-member identity cover, repeated refinement indices, non-separated base, and covers with non-quasi-compact members. The argument uses only finitely many affine opens over each affine chart and imposes no global qcqs hypothesis on the base. Every cited node was opened and its statement read; citations.json contains their verbatim statements with the correct step numbers. Every non-elementary input is named, while the cover, tensor-factor and disjoint-union calculations are written out. All five steps have fewer than 2000 characters. Generic off-unit inputs are declared in split_report.tool_uses. No new statement, hollow construction, statement dispute, or hidden appeal to a dependency's proof remains.
