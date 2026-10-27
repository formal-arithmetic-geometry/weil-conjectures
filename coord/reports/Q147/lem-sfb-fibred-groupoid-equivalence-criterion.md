## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-fibred-groupoid-equivalence-criterion.json: statement, split; no exact Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-chosen-object-quasi-inverse.json: statement, unsplit; no exact Mathlib match for the construction extending prescribed object representatives and comparison isomorphisms.
- citations.json: exact statement quotations for all three dependency occurrences in the five proof steps.

## Attachments

None. Searched the exact blueprint tag and the fibred/fibered/groupoid/IsFibered terminology in lean/WeilConjectures/. No declaration there states this criterion, or the new prescribed-choice construction. No Lean was written and no compiler was run.

## Wanted sources

None. Both source lemmas are present in literature/stacks-project/categories.tex.

## Findings and corrections

The item statement is unchanged and true. Its proof was empty. Tag 003Z supplies both the fibrewise Hom argument and an inverse over the base; its proof explicitly invokes the ordinary prescribed-choice construction and omits some verification of the vertical comparisons. Those verifications are now written out. The new node records Tag 05SG, including the characterization of the comparison JF to the identity obtained by lifting the inverse of i at F(A); this is the construction explained in the final paragraph of the source proof, not an added hypothesis.

The existing leaf lem-trf-fully-faithful-ess-surj-equivalence proves ordinary existence of an equivalence only. It does not state that the inverse extends a specified object function or that its comparison components are the specified ones. Citing its proof for that additional property would be C4. The new node therefore preserves the prescribed choices, which are exactly what the over-base argument needs. It does not restate fibrewise full faithfulness, the criterion's conclusion, or any clause of the criterion: it concerns arbitrary ordinary categories, with a total fully faithful functor as hypothesis and explicit chosen comparison data. It contains no fibred-category theorem.

The inherited blueprint ancestor is null (tools/blueprint_refs.py ancestor confirms this), with the inherited long via chain ending at the historical direct-image alteration argument. I preserved that provenance. I also read the current blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images and unit proof files in literature/blueprint/latest/. Paragraph (3) currently uses proper and open direct image and compactification. This delivery proves only the assigned generic stack-equivalence prerequisite and changes no unit route, chapter or target.

## Not duplicates

lem-sfb-chosen-object-quasi-inverse vs lem-trf-fully-faithful-ess-surj-equivalence: the existing statement concludes that some quasi-inverse exists, while the new statement extends a prescribed object assignment and prescribed comparison isomorphisms, determines its arrow map, and characterizes the opposite comparison; the existing source mentions 05SG only in support of ordinary existence.
lem-sfb-chosen-object-quasi-inverse vs lem-sfb-adjunction-generator-defect-criterion: the existing statement is a triangulated-generator criterion and does not state the construction for arbitrary ordinary categories with prescribed representatives; 05SG appears in proof-source metadata, not as that statement.
lem-sfb-chosen-object-quasi-inverse vs lem-pur-raw-localization-finite-product-equivalence: the existing statement concerns scalar extension of raw localizations and product equivalences of linear categories; its proof's citation to the ordinary quasi-inverse construction is not a statement of the generic prescribed-choice lemma.

Searches of the whole DAG for 05SG and lemma-construct-quasi-inverse found those three relevant existing files. Searches for 003Z identify the item and its parent. Broader keyword searches and tools/blueprint_refs.py searches for fibred, fibred groupoid, 003Z, 05SG, quasi-inverse, quasi inverse, fully faithful functor and prescribed found no node stating the prescribed-choice lemma. All Mathlib searches were run with the required msearch.py command and are recorded verbatim from searches.jsonl. Two distinct semantic formulations were used for both the criterion and the prescribed-choice construction. Read HasFibers.lean:65-106, FiberedCategory/Grothendieck.lean:110-142, Equivalence.lean:606-649, Functor/FullyFaithful.lean:80-118,143-242,390-409 and EssentialImage.lean:174-192. The fibre-model equivalences are not the criterion. asEquivalence and essImage.liftFunctor select their own preimages and do not state extension of prescribed representatives. The natural-isomorphism cancellation and preimageIso results provide pieces, not the complete new statement in one specialization.

## Review by Q147

I read the full statement and proof of Stacks Tag 003Z (lemma-equivalence-fibred-categories), Tag 05SG (lemma-construct-quasi-inverse), and the converse argument in Tag 003V (lemma-fibred-groupoids). For the item I checked the base categories, fibre groupoids, existence of cartesian lifts, cartesian preservation by G, and fibrewise bijections and essential surjectivity against the source. No hypothesis is added. The source's stronger-equivalence terminology is expanded by precisely the vertical isomorphisms required here.

Step 1 uses the cartesian universal property and the fibrewise Hom bijections already in the hypotheses: arrows with a fixed base u factor uniquely through v by a vertical arrow, and preservation of v gives the identical factorization in B. The morphism maps intertwine because G preserves composition. Their disjoint union gives total full faithfulness, including base categories with multiple endomorphisms. This is a direct universal-property calculation, not an uncited full-faithfulness criterion.

Step 2 cites def-weil-size-convention only for its universe convention: I read that statement, which fixes U in V and categories in the larger universe. The item's explicit small base and small fibres make the simultaneous choice set-sized. It uses essential surjectivity inside B(T), not ordinary essential surjectivity, to choose vertical i_b and a_b over the exact original T.

Step 3 cites the new node's complete statement, which gives exactly the functor on the prescribed objects, the arrow-map equation, and both natural isomorphisms, with G(e_a)=i_{G(a)}^{-1}. Its total full-faithfulness hypothesis was proved in Step 1 and its choice data were supplied in Step 2. It is the only non-elementary step and the new node is statement-only. Step 4 cites that same statement for those equations; applying the projections to them gives pH=q on arrows and the identity base map for each e_a. The i_b were already vertical. Thus neither verticality nor strict preservation of the base is inferred from an arbitrary ordinary equivalence.

Step 5 needs no additional theorem: an arbitrary arrow w factors through a chosen cartesian lift v with an invertible vertical factor t. Factoring through v and then through t inverse gives the required unique factorization through w. This proves cartesianness directly, as in 003V, rather than citing an absent node for 'all arrows are cartesian'. It applies in A, and hence every value H(f) is cartesian. The two-step universal-property argument is elementary and was kept inside the item, not inflated into a new node.

I checked empty bases and empty fibres: essential surjectivity prevents a nonempty target fibre paired with an empty source, and all choices over an empty base are empty. For a terminal base the proof is the ordinary groupoid equivalence construction; for a base with noninvertible arrows Step 1 works separately over every arrow and Step 5 uses only invertibility of vertical factors. In the new node an empty target category forces the source empty when F exists; fully faithful functors with multiple isomorphic object representatives still give a unique arrow function once j and i are fixed. Identity functors and nontrivial automorphisms satisfy the stated equation for e, so the inverse orientation is correct.

Against delivery-errors B–E: the one new node is self-contained with its notions defined or cited, has the correct Stacks tag/label, genuine logged searches, no proof or proof dependencies, and complete provenance; it is not an elementary fact or a duplicate. Every citation was read as a statement and copied verbatim to citations.json. Elementary arguments are written explicitly. There is no cycle (the new node uses only size and category definitions), off-unit theorem dependency, hidden alteration route, or SGA citation. Each proof step is under 600 characters, so no step exceeds the long-step review threshold. No statement dispute was found.

## Unfinished work

No assigned stage-1 work is intentionally omitted. The new 05SG statement remains unsplit for the next worker, as required. Mechanical validation and direct delivery follow this review.
