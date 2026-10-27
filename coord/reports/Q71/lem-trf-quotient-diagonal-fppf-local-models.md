## Worker report

Files written: `dag/nodes/sec-trace-formula/lem-trf-quotient-diagonal-fppf-local-models.json` (statement, split; no exact Mathlib match), `citations.json`, and this report. The search command also wrote `searches.jsonl`. No new nodes and no new Mathlib leaves.

Attachments: none. Searched the live `lean/WeilConjectures/` by the blueprint id and quotient/diagonal/fppf/kernel-pair terminology; there is no declaration stating this item. No Lean was written or compiled.

WANTED: none.

The statement is unchanged. The imported node had no proof. The split follows Stacks `spaces.tex`, Tag 0265, `lemma-presentation-quasi-compact`, third representability step: the cartesian square and cube give precisely the stated local pullback. The source chooses an etale covering using representability of the quotient map proved earlier; the item explicitly asks instead for a common fppf covering from simultaneous local lifts. Successively applying the general sheafification section lemma gives that covering without assuming the surrounding representability theorem. This preserves the specified local-model route and avoids a dependency on the parent theorem.

All work requested for this item is complete, subject to the required server dry run and delivery. No outstanding mathematical gap is left in the assembly proof; the existing nodes used remain their own independent obligations.

## New nodes

None. The generic sectionwise local-lifting theorem, quotient kernel-pair isomorphism and separated/local-quasi-finite base-change theorem already exist. The equality-sheaf calculation and evaluation of the scheme pullback are elementary assembly steps, not new lemmas.

## Not duplicates

No new nodes were created. Searched the whole DAG by sheafification, quotient/relation, diagonal, subcanonical and base-change terminology, and opened the matching statements. Blueprint searches for `quotient sheaf`, `sheafification`, `diagonal` and `kernel pair` found no other blueprint statement of the item. Reused `lem-trf-etale-relation-kernel-pair` rather than creating a duplicate of the quotient-effectiveness assertion, and reused `lem-weil-pbc-separated-lqf-base-change` rather than another permanence lemma.

## Mathlib searches

Retained every inherited search and added the seven actual command searches in `searches.jsonl`, with the exact tool and query. Read every hit. The first Loogle query reported an unknown identifier, which is preserved as a diagnostic rather than evidence of absence; the second valid Scheme/pullback query returned open-immersion and scheme-pullback results. Both LeanFinder phrasings returned scheme gluing/diagonal and monomorphism results, not this quotient-sheaf assertion. LeanSearch returned sheafification lifts and ring/topological quotient lifts. Read Mathlib `AlgebraicGeometry/EffectiveEpi.lean:55-95`, `Sites/ConstantSheaf.lean:65-85`, `Pullbacks.lean:665-673`, and `CategoryTheory/Sites/Sheafification.lean:170-172,194-202`. They respectively concern descent along given affine flat surjections, continuous-map sheaves, diagonals of existing scheme morphisms, and the sheafification universal property; none supplies every clause of this item as a one-line specialization. Earlier recorded service unavailability is retained as unavailable.

## Review by Q71

I read the item and the source `spaces.tex:1466-1604`, Tag 0265, `lemma-presentation-quasi-compact`, including its cartesian square/cube and the final base-change sentence. I also read `sites.tex:2157-2183`, Tag 00WK, `lemma-sections-sheafification`; `groupoids.tex:3790-3816`, Tag 045Y, `lemma-quotient-pre-equivalence`; `schemes.tex:4289-4327`, Tag 01KU, `lemma-separated-permanence`; and `morphisms.tex:3925-3958`, Tag 01TM, `lemma-base-change-quasi-finite`. There are no new node statements to compare with sources. The chapter and sk-i-curve-zero unit were read: this is the existing lower-level quotient-presentation subargument and changes neither their statements nor their route. No SGA source is used.

Step 1 uses the sheaf equalizer condition actually stated in `def-weil-pbc-sites-and-cohomology`. I checked the diagonal fibre sectionwise: its extra section is uniquely the common value, so it is a singleton or empty, not a set of arbitrary relations. Local equality implies global equality by uniqueness in F's sheaf condition. This is an elementary proof of the sheaf assertion and does not require a separate finite-limit theorem or subcanonicity node.

Step 2 uses the local-section existence clause of `lem-weil-pbc-site-sheafification-sections-local`, whose statement I opened. It applies to the presheaf of SET quotients in the stipulated sufficiently large universe. Choosing representatives is ordinary choice in a set quotient. Applying it over each first covering member and then using the composition axiom in `def-weil-pbc-sites-and-cohomology` gives a single covering carrying both lifts. I included the evaluation-at-identity argument for maps from h_T, so no full-faithfulness-only Yoneda citation is asked to supply the general Yoneda lemma. The citation quote for this step includes the covering composition clause itself.

Step 3 uses the actual ISOMORPHISM clause in `lem-trf-etale-relation-kernel-pair`, not merely the locally surjective map in the Stacks prototype. I checked its hypotheses: R and U are S-schemes, j is a monomorphism, its image on each test scheme is an equivalence relation, and the quotient is the same big-fppf sheafification. The statement needs neither affineness nor etaleness, so our etale hypotheses cause no mismatch. Evaluation of the isomorphism gives global unique witnesses. The source Tag 045Y alone would only give local witnesses; I deliberately cite the stronger existing kernel-pair node.

Step 4 uses the full universal property and existence of arbitrary scheme fibre products in `def-pc-fibre-product`, which I opened, together with the kernel-pair node cited explicitly again. A W-point OVER T_i has fixed first component w, and its second component r satisfies s r=u_i w and t r=v_i w in that order. I wrote the two inverse maps and checked restriction by precomposition and uniqueness; no unproved descent or representation identification is hidden in this step. The notation h_Y here is relative over T_i as in the item.

Step 5 uses both clauses of `lem-weil-pbc-separated-lqf-base-change`, whose statement I opened. Its f is exactly j and its base map is (u_i,v_i), so its hypotheses match the two explicitly assumed properties. It imposes no finiteness on the base change. This and the general local-sheafification theorem are generic tools from sk-thm-p1; the reasons are declared in split_report.tool_uses for maintainer review, not in the maintainer-owned tool_uses field.

I tested the empty scheme/empty cover case (F(empty) is a singleton, so the equality presheaf still satisfies the sheaf condition); the identity relation (local models are coincidence subschemes); equal sections (the relation witness exists uniquely on every test object); and unequal sections (no witness on that object, with equality allowed after restriction). The proof never infers scheme factorization from set-theoretic image containment. It handles arbitrary nonseparated S and nonaffine U because only the assumed properties of j are pulled back. No statement dispute was found.

I checked B-E point by point: no new unsplit proof or self-contained-statement issues, no invented search records, no new duplicate or clause-restatement nodes, every non-elementary ingredient is the statement of a cited node, and the new proof avoids the parent representability result and hence its cycle. Every used node has a verbatim statement quote in citations.json. All five proof steps are below 2000 characters (the full assembly text is below 3000); none hides a long standard lemma. During self-review I added the kernel-pair citation again in step 4 and corrected the step-2 quote to cite the site composition axiom rather than its sheaf-condition clause. No outside file was modified.
