# Worker report

Group Q48; item lem-trf-local-open-representatives-support-descent; stage 1; 2026-10-23.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-local-open-representatives-support-descent.json: split statement; no Mathlib match for the complete assertion; statement and statement dependencies unchanged.
- citations.json: nine step/node pairs with literal statement quotations, checked against the current read DAG.
- report.md: this report. searches.jsonl is the unmodified output log of the required search command.

No new nodes, hence zero new Mathlib leaves. No Lean or compiler commands were used. Everything written is in the assigned sandbox. There was no previous item copy, split, report or search log when this run started; the sandbox initially held only dispatcher brief markers.

## Attachments

None for this item. The exact blueprint-tag search in lean/WeilConjectures and searches by local-open/support-descent, open representatives, presheaf/functor and representation found no project declaration of this assertion. The related Sheaf/AlgebraicGeometry/SpaceOpenImmersionEtaleLocal.lean is a different statement and its proof contains sorry. The existing node lem-weil-pbc-open-subscheme-fpqc-descent is already attached to AlgebraicGeometry.openSubscheme_existsUnique_of_fpqc and has a closed audit; it is a dependency, not an attachment of the present item.

## WANTED

None. All needed sources are present in literature/stacks-project/.

## Corrections and retained route

No statement dispute or correction. The arbitrary-presheaf assertion is true without a sheaf condition or compatibility of the local representing isomorphisms. The proof does not claim that F is globally represented by the descended open: that additional sheaf assertion is the separate sibling lem-trf-prescribed-open-fppf-sheaf-representation. The local representatives force their supports to agree simply by evaluating the two bijections on the pulled-back opens themselves.

Read the chapter sec-trace-formula, unit sk-i-curve-zero and current literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md. The ancestor proof concerns contraction and trace-locality; the inherited via chain places this geometric helper below its polarized-descent branch. This split only supplies the support argument explicitly requested by steps 2-3 of lem-trf-space-open-immersion-etale-local; it changes no chapter, unit or route. The item is not the unit key node, so no unit realization record is changed. No stage-1 repair note exists for the item.

## Existing-node and Mathlib searches

Searched all dag/nodes for Tags 041X and 03N0, for open/subfunctor/descent, local representatives, etale open maps, fppf/fpqc comparison, fibre-product points and base-change image. Read the exact statements of the existing open-subscheme fpqc descent, invariant-open-image-pullback, etale/fpqc comparison, and the fppf-to-fpqc node. The already existing compatible-open descent theorem is the correct final dependency; no new support-descent theorem is needed. The more specialized invariant-open-image theorem assumes a flat quasi-compact surjective singleton and is unnecessary here. The small-etale-to-fpqc comparison has small-site objects in its statement, so the present proof instead uses the general fppf-cover comparison after checking its definition.

Ran tools/blueprint_refs.py ancestor for the item and search for 'open subschemes', 'open representatives' and '03N0' on the full imported blueprint. The first returned eighteen broad matches (limit opens, Zariski site and other unrelated notions); the latter two returned none. None states the arbitrary-presheaf support assertion; same_as remains []. Retained the precise inherited from.place and via chain.

Ran all four prescribed search kinds through batch2/msearch.py under this group and item, with two different semantic phrasings and a second candidate-name grep. Read every result. Sites/Representability.lean:40-100 assumes a Zariski sheaf together with relatively representable open maps into it; it does not give the present assertion about restrictions of an arbitrary presheaf. FlatDescent.lean:133ff descends the property of an existing scheme morphism. Topological sheaf gluing and inverse-image restriction lemmas are different statements. The second semantic search returned isoOfEq names; the candidate-name grep did not find these in the pinned AlgebraicGeometry source. All six actual queries are appended to the item's retained historical searches with their command-log records and verdicts; no historical search was rewritten or invented.

## Not duplicates

No new nodes were created. Existing general lemmas are cited directly. The item adds automatic overlap equality from local presheaf representations to the existing compatible-open descent theorem; it does not duplicate that theorem.

## Review by Q48

I read Stacks spaces-descent.tex Tag 041X, label lemma-descending-property-open-immersion, including its passage from equality of the two pulled-back opens to an open downstairs by Tag 03N0. I read descent.tex Tag 03N0, label lemma-open-fpqc-covering, with its existence and uniqueness and its lack of any finiteness or quasi-compactness restriction on the family or schemes. I also read schemes.tex Tag 01JY, label lemma-base-change-immersion, topologies.tex definition-fppf-covering in Section 021L, and Tag 022C, label lemma-zariski-etale-smooth-syntomic-fppf-fpqc, including the affine-local finite-subcover proof. The present proof_origin is agent because the evaluation argument for an arbitrary presheaf is an explicit generalization of 041X rather than a verbatim proof in that source. There are no new-node sources to audit.

Step 1 uses the actual statement of lem-weil-pbc-open-immersion-base-change: an open immersion pulled back by any scheme morphism remains an open immersion. It applies with W_i -> T_i and R -> T_i, and separately W_j -> T_j and R -> T_j; it requires no property of the projection. def-pc-fibre-product gives the two projections and universal property, and def-weil-open-immersion identifies each resulting scheme with its open support and restricted structure sheaf. These are exactly the two inverse-image opens the conclusion compares.

Step 2 is elementary with the argument written out. Regard A over T_i and T_j by the two projections. Its maps to T agree because R is their fibre product. The projection A -> W_i gives an element of F(A) through alpha_i; the component bijection alpha_j on that same scheme A gives A -> W_j over T_j. The pair of maps into R and W_j satisfies the fibre-product equation, so def-pc-fibre-product supplies A -> B over R. Thus the underlying open of A is contained in that of B; swapping i,j proves equality. def-weil-open-immersion states that the scheme on an open is the restricted structure sheaf, so equality of supports is equality as open subschemes. This does not use Yoneda, sheaf gluing, or a claim about morphisms that the cited nodes do not state. The argument is under 1000 characters and hides no separate non-elementary comparison lemma.

Step 3 opens and uses three exact statements. def-weil-etale-morphism explicitly includes flatness and local finite presentation. def-pc-fppf-site defines covering families by those two properties and joint surjectivity. The item assumes the latter, so the hypotheses of lem-trf-fppf-covering-is-fpqc hold; that node explicitly says the SAME family is fpqc. Thus there is no mistaken use of a singleton qc hypothesis or of an uncited affine-refinement theorem. The finite refinement needed to be fpqc is supplied by the cited comparison, not assumed of the original family.

Step 4 uses only lem-weil-pbc-open-subscheme-fpqc-descent. I opened its statement and verified that it asks for an fpqc family and equality of the two pulled-back opens for every pair; steps 3 and 2 provide exactly those. It explicitly supplies a unique open subscheme with every prescribed inverse image. Its closed Lean audit makes it an authorized generic tool without an off-unit route declaration. All other statement dependencies of proof steps are definitions or Mathlib leaves. Each of the nine step/node citations has a verbatim substring quote in citations.json; none relies on the proof of a cited node.

Checked delivery-errors B-E against the written files: no new statement-only task or hollow definition is introduced; source tags and labels match local TeX; no source section number is substituted for a tag; the argument is a proof rather than a relabelling into new nodes; no non-elementary fact is left as an uncited tag. The two non-elementary cover/descent facts and the base-change fact are cited nodes. All step lengths are below 2000 characters. The statement and stmt_deps are unchanged, proof_deps is exactly the union of uses, and the final check is left to the required server dry run.

Small cases checked: I empty forces T empty by joint surjectivity and the unique descended open is empty; empty members and empty pairwise overlaps cause no problem, because the inverse component bijections are evaluated only on existing objects and the pulled-back empty inclusion is legitimate. W_i empty and W_i = T_i give respectively empty/full supports wherever the hypotheses permit them. A singleton identity cover gives U = W_i. Disjoint components and two copies of an identity cover show explicitly why incompatible supports could not admit the specified bijections. Infinitely many covering members and non-quasi-compact schemes are handled by the actual covering comparison and descent statement, with no global finite-subcover claim. No nilpotent or reducedness condition is used: equality is between open subschemes with the same restricted structure sheaf.

## Unfinished work

None in the split. The required server dry run and push are the delivery verification below.
