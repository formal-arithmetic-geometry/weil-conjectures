# Stage-1 delivery: lem-sfb-triangular-maximal-torus-conjugacy

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-triangular-maximal-torus-conjugacy.json: item, split into seven steps; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-multiplicative-type-transporter-smooth.json: one new statement, unsplit; no Mathlib match. This is a general theorem about containment transporters between multiplicative-type subgroups, not a renamed clause asserting the PGL2 conjugacy conclusion.
- citations.json: verbatim statement excerpts for every cited node in each step.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag, triangular tori, PGL, diagonalizable groups and transporter found no declaration of this relative assertion. The existing line-bundle/torsor node is already Lean-closed and is reused as a proof input, not offered as an attachment to this item.

## Sources wanted

WANTED: Brian Conrad, Reductive group schemes, Proposition 2.1.2, printed pp.56--59, and Proposition 4.2.7, final proof paragraph, printed p.124; locally as literature/conrad-reductive-group-schemes.pdf, for the item and lem-sfb-multiplicative-type-transporter-smooth. Read the PDF online at the source URL in the nodes. It is absent from the read-only literature directory. I have not changed literature or downloaded into the repository. The item's proof_origin is by agent and explicitly records the online reading and missing local archival copy. No SGA source was used.

## Audit of the imported item and route

The statement is retained verbatim. No STATEMENT-DISPUTED correction was needed. The source's transporter initially means containment; our item's transporter means equality. Step 3 explicitly supplies the missing identification using relative character duality. Likewise a calculation only on geometric points would not justify equality of normalizer schemes in characteristic 2 or over a nonreduced base. Step 1 instead works over every ring and compares Laurent coefficients.

I read SETUP's three levels, the chapter and unit records, GOAL.md, the standing brief, the whole B--E checklist in both copies of delivery-errors.md, and tools/README.md. The current latest blueprint is main-20261024. Its sk-thm-sf-ctf-stability section and sk-thm-sf-ctf-stability-direct-images proof (3) were read; this supporting item lies down the inherited rank-one matrix-model chain. The ancestor tool returns None, so no blueprint ancestor was invented. Its inherited from.node, from.place and via chain remain intact. The new node adds the item to that via chain and identifies the precise supporting sentence and Proposition 2.1.2. This is not the unit's key node, so no unit record was changed.

## Searches and why only one new node

The parent item's original Mathlib search records were retained. I reran its queries with msearch.py for Q29 and inspected the returned matrix, ordinary-torsor and scheme-locality signatures. New transporter searches used LeanSearch, LeanFinder in two formulations, Loogle and grep; all are recorded exactly in the parent sandbox searches.jsonl and the new node's mathlib_searches. An additional full-Mathlib grep found diagonalizability of individual endomorphisms (Semisimple.lean, especially lines 77--85), not a theorem about subgroup-scheme transporters. LeanSearch smoothness hits provide the definition and local finite presentation, not representability of this functor. No leaf match was found.

Before creating the node, I searched all dag/nodes statements and sources for transporter, multiplicative type, Conrad 2.1.2, normalizer and conjugacy. I ran blueprint_refs.py search for transporter, torus, multiplicative type, multiplicative, normalizer, smooth closed and conjugate, and checked the relevant latest-blueprint text. There was no duplicate transporter node. I read the source statements of the existing geometric maximal-torus conjugacy, relative torus normalizer, relative character duality, split-torus torsor geometry and line-bundle torsor nodes. The first and last give exactly the field conjugacy and etale-to-Zariski input needed here; the normalizer node concerns only the same split torus, and the split-torus frame geometry requires a field base. Neither covers the new arbitrary-Noetherian-base containment transporter.

## Not duplicates

lem-sfb-multiplicative-type-transporter-smooth vs lem-sfb-relative-torus-centralizer-normalizer: the existing node represents the centralizer and self-normalizer of one supplied split torus and gives Lie and character-stratum information; the new node represents containment from H to an independently supplied H', which may be nonsplit or nonreduced and need not have equal rank. The self-normalizer statement alone cannot supply a transporter or its smoothness before conjugacy exists.

lem-sfb-multiplicative-type-transporter-smooth vs lem-sfb-triangular-maximal-torus-conjugacy: the new node has no PGL2, maximality, surjectivity, conjugacy, torsor or local-section conclusion; it can be empty. The item's matrix calculation, geometric maximality, containment-to-equality comparison, torsor inverse and line-bundle step are still proved in the item.

## Review by Q29

I checked the item directly against Conrad Proposition 4.2.7's last paragraph on printed p.124. I read Proposition 2.1.2 on printed p.56 and its proof pp.57--59 for the new input. That proposition uses the containment transporter defined in Section 2.1, assumes finite presentation and affineness of the ambient group, and gives smoothness when both subgroups are of multiplicative type. Our new statement restricts to an affine Noetherian base, where its finite-type hypotheses imply finite presentation. Its base-change clause is the equality of the same functor after restricting the test schemes, not an additional invariance assertion about points. In the source it is not asserted that this transporter is nonempty, which is why that hypothesis and conclusion are absent from the new node. I also read Milne Theorem 17.10 and its solvable-case reference in the local algebraic-groups PDF, and Stacks Tag 0CFV (spaces-topologies.tex, lemma-etale-dominates-smooth) and the underlying Tag 055V (more-morphisms.tex, same label) for the existing etale-section input. The latest blueprint line-bundle/torsor statement was read as well.

Step 1 uses the projective-frames node for local matrix representatives and their scalar ambiguity. Dividing by the invertible lower diagonal entry is scalar-invariant, so it really glues and gives the affine B chart. The affine-space smoothness node and open-restriction Mathlib leaf give smoothness of this chart; they are not cited for any conjugacy fact. Matrix multiplication gives the group law, and the universal unit t forces the upper off-diagonal coefficient x to vanish for a normalizer element. I checked that no division by 2, no reducedness and no assumption that there are many units in R enter this calculation: t lives in R[t,t^{-1}].

Step 2 uses the full statement of lem-sfb-borel-maximal-torus-conjugacy, which allows any smooth connected affine finite-type group, not just a reductive group. The group used is B_F, not PGL2. Its coordinates give connectedness directly using the dense zero prime of the domain F[a,a^{-1},x]. D is maximal in B because its centralizer is D by the calculation in step 1; T is maximal in B because it is maximal in PGL2 by hypothesis. Thus the cited conjugacy result applies with all of its hypotheses and gives equality of subgroup schemes, not only equality of rational-point sets.

Step 3 uses the new node for exactly closed representability and smoothness of the containment transporter. Here B is affine smooth finite type over the original Noetherian ring, and T and D are closed and fppf locally products of Gm, so the hypotheses hold. The relative character-duality node states the locally constant lattice-map description for homomorphisms over arbitrary rings, including nonreduced rings. On a splitting cover the inclusion into D is an isomorphism on every geometric fibre by maximality; its locally constant lattice map therefore has rank one and exponent +1 or -1. This proves an actual local inverse before specialization. Equality then descends since the two subgroup functors are sheaves. I did not invoke a fibre criterion lacking flatness or finite presentation, nor assume at the outset that T is split globally. This is the comparison missing between the source's containment convention and the item's equality convention.

Step 4 cites the exact smooth-surjective etale-section statement of lem-sfb-smooth-space-cover-etale-sections. Its source may be an algebraic space, hence includes the represented scheme Y. Surjectivity follows independently from the geometric points supplied in step 2. No field-base hypothesis was smuggled in.

Step 5 is elementary group algebra: the natural inverse is (y1,y2) -> (y1 y2^{-1},y2); its first component normalizes D and hence belongs to D by step 1. This gives the required left action, with the order of multiplication checked. It is an isomorphism of functors on all test schemes and thus of represented schemes, avoiding any unsupported reduction to geometric points.

Step 6 uses precisely the etale clause of the existing line-bundle/torsor node: every Gm-torsor on the small etale site is a frame torsor of an invertible O_S-module. This is available for every scheme S, not just curves or field schemes. The cited definition says the module is locally isomorphic to O_S. Each Zariski open is an object of the etale site, so its frame corresponds directly to an actual section of the represented Y. No unquoted representability theorem for the frame torsor is needed, since Y has already been represented in step 3. In particular this reasoning does not claim Pic(S)=0.

Step 7 is restriction of a subgroup-functor identity along W -> S_i and then along each V -> W. It explicitly gives the claimed compatibility after arbitrary base change. This uses the full functor equality, not equality only at geometric points.

I checked B--E point by point: new node self-contained and statement-only, all notions inline or with their defining nodes, exact searches logged, no prohibited SGA route, no new node restating an item clause, every non-elementary fact supplied by its cited statement, proof_deps exactly the union of uses, and citations.json quotes copied verbatim. No proof step exceeds 2000 characters (the longest is the explicit character-map comparison at 1540). Edge cases checked: T=D (Y=D); conjugates by a unipotent upper triangular element; characteristic 2 with a nilpotent off-diagonal x; A a product of two rings; nonreduced A; and empty subsequent base changes. For the new node I checked H=H'=1 (Z=G), H=1 (Z=G), and H=Gm,H'=1 inside Gm (Z empty), as well as nonreduced multiplicative-type groups such as mu_p in characteristic p. These cases confirm that its empty-transporter allowance is necessary.

## Unfinished work

None for this one-level split. The single new general transporter node is intentionally unsplit and joins the stage-1 queue. There are zero new Mathlib leaves. All writes are sandbox artifacts or search-command logs; no project source, Lean file, launcher script or compiler was used.
