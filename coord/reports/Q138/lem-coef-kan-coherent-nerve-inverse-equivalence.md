# Stage-1 report: lem-coef-kan-coherent-nerve-inverse-equivalence

## Files written

- dag/nodes/sec-six-functors/lem-coef-kan-coherent-nerve-inverse-equivalence.json — statement node, now split into four steps; no Mathlib match for the item.
- citations.json — one verbatim statement quotation for every step/node citation.
- report.md — this report. searches.jsonl records the actual Q138 searches; write_split.py is sandbox-only preparation code.

No new nodes and no new Mathlib leaves. The existing leaf lem-cbc-kan-functor-space-kan is reused. The item's statement, statement dependencies, historical blueprint ancestry, chapter, unit and inherited search records are preserved.

## Attachments

None. Searched all of /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the blueprint id and coherent-nerve/SimplicialNerve spellings; no declaration states this item. The Mathlib declaration of SimplicialNerve is a definition, not a theorem supplying the requested inverse triangles. The exact upstream master checkout was not treated as evidence of finished proofs.

## Literature wanted

WANTED: archival Kerodon Proposition 2.4.6.10 (00M5), Example 2.4.3.10 (00KX) and Remark 2.4.6.4 (00LW), for lem-coef-kan-coherent-nerve-inverse-equivalence. Read https://kerodon.net/tag/00M5, https://kerodon.net/tag/00KX and https://kerodon.net/tag/00LW online on 2026-10-17.

WANTED: archival Kerodon Corollary 3.1.3.4 (00TN) and Theorem 2.4.5.1 (00LJ), for the already-existing dependencies lem-cbc-kan-functor-space-kan and lem-coef-kan-coherent-nerve-quasicategory. Their statements were read online at https://kerodon.net/tag/00TN and https://kerodon.net/tag/00LJ.

These are Kerodon identifiers, not Stacks tags. No Stacks result supplies this enriched simplicial-set construction. No SGA reference is used. Because the item is proved by an explicit calculation in the project's convention and these references are not archived locally, proof_origin.by is agent.

## Findings and corrections

The imported child had no proof. The statement is sound and needs no correction. Its source description must be interpreted with care: Kerodon's path-poset convention gives an edge from the composite to the long edge (00KX), whereas the project's inclusion poset has {0,2} contained in {0,1,2}, giving the reverse orientation. I did not silently identify the two simplicial constructions or assume a convention-comparison theorem. Step 2 produces the actual orientation needed in the project by a single outer-horn filler, and steps 3–4 construct enriched functors directly. There is no statement dispute.

Read both versions of the ancestor prop-coef-integral-exceptional-adjoint: the historical master file has the mapping-adjunction calculation and triangle identities in proof paragraph 2; main-20261015, under sk-thm-sf-package, retains the adjunction statement but has no proof section. The existing descendant's recorded chapter/unit/ancestry is retained. The item is a generic verification within the recorded mapping-adjunction route and does not replace the ancestor's coefficient or geometric argument. It is not the key statement of sk-prop-sf-biduality-general, so the unit's realized fields are untouched.

## Unfinished work

None in the one-level split. The existing quasicategory theorem remains a cited dependency; this delivery does not claim its downstream proof is finished.

## Not duplicates

No new nodes. Whole-DAG concept searches found lem-cbc-kan-functor-space-kan and lem-coef-kan-coherent-nerve-quasicategory, and both are reused. Blueprint searches for coherent nerve, homotopy inverse and Kan found no blueprint statement of this item. No additional equivalent blueprint node was found, so same_as remains empty.

## Review by Q138

I read the item's source 00M5 together with its explicit two-simplex example 00KX and the homotopy-orientation discussion in 00LW. I read the two cited theorem sources 00TN and 00LJ, and opened the complete statements of every cited DAG node, especially the internal-functor formula and the subset-poset/union model in def-coef-infinity-category-of-spaces. No new-node source requires review.

Step 1 takes exactly Kan closure of Fun(K,Z) from lem-cbc-kan-functor-space-kan. The domains A and B are simplicial sets and the targets A and B are Kan in the same universe, so both applications satisfy its hypotheses. The general application to all small Kan pairs supplies local Kan enrichment. The statement of lem-coef-kan-coherent-nerve-quasicategory explicitly asserts that the coherent nerve of this category is a quasicategory; I did not take that from a definition. The definitions of spaces and Fun identify the assumed simplicial homotopies with actual mapping-set edges. This step is marked non-elementary and cites both theorem nodes.

Step 2 uses the Kan horn-filling definition, with the Kan condition already established in step 1. Its horn is the outer horn with missing edge 12, not an inner horn: the specified edges 01 = e and 02 = id_u agree at vertex 0, and the filler has edge 12 from v to u. This is one application of a definition with the boundary data written out, so it is elementary and does not deserve a separate reversal lemma node. It normalizes each of the independently supplied homotopies, preserving the specified maps f and g.

Step 3 uses exactly the subset-poset formula, union composition and coherent-nerve simplex definition in def-coef-infinity-category-of-spaces. I listed every nonempty mapping set of the three-object source. There is only one nonunit composition, and its union endpoint is the value gf of h_A. All other compositions have an identity factor or empty domain. Thus this is a finite check of the definition, not an invocation of the general theorem describing all enriched triangles. Restriction to each face explicitly yields f, g, 1_A, and the identity/degeneracy identification is checked from the constant monotone map.

Step 4 spells out the analogous assignments for B,A,B and the union endpoint fg, rather than leaving their compatibility implicit. The exact equivalence-edge definition in def-cbc-enhanced-diagrams-cones requires precisely these two inverse triangles, so it applies to the quasicategory established in step 1. No higher coherence or connectedness hypothesis is needed for that definition.

I checked the empty case: Fun(empty,empty) is the point simplicial set, identities and all degeneracies exist, and the construction is constant. With exactly one empty complex, the assumed pair of maps cannot exist. With identities or constant homotopies the interval map may be constant, which remains an enriched functor. For disconnected nonempty complexes no chosen point is used. I checked universe size using the item's containing-universe convention, so no colimit or large-index existence theorem is hidden.

Against delivery-errors B–E, the statement remains self-contained, all notions come from its two existing statement dependencies, every non-elementary theorem used is a cited statement, and every citation has an exact quotation. New-node forms/searches/source tags and duplicate-pair reports are inapplicable because no nodes were created. The construction carries the argument instead of moving its clauses to new nodes. Step lengths are 732, 720, 1397 and 1198 characters, all below 2000; the elementary steps contain only the stated horn filler or finite definition checks, with no standard subclaim hidden inside.

The Q138 searches used leanfinder twice with different phrasings, leansearch, loogle and grep through msearch.py; all responses were available and were read. Hits concern ordinary nerves or truncated homotopy categories, not the enriched triangle criterion. I read Mathlib/AlgebraicTopology/SimplicialNerve.lean lines 20–34 and 193–209 and candidate ordinary nerve/homotopy-category declarations. SimplicialNerve still lists its basic identifications and quasicategory result as projects. The Kan-exponential instance at AnodyneExtensions/PushoutProduct.lean:155–156 is already the cited Mathlib leaf; no duplicate was made. No search that was not run was added.
