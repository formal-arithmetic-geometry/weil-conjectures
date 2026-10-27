# Worker report

Item: lem-sf-cbc-normalized-augmentation-transport. Group: NU. Stage 1, direct delivery, 2026-10-22.

## Files written

- dag/nodes/sec-smooth-purity/lem-sf-cbc-normalized-augmentation-transport.json: statement; split into six elementary categorical calculations; no exact Mathlib match for the whole statement.
- report.md: this report and the direct worker's mathematical review.
- citations.json: one verbatim statement quotation for each of the six proof-step citations of def-nagata-category.
- searches.jsonl: seven searches actually run through the mandated msearch.py command. The item's five inherited Mathlib search records were retained, and seven fresh records were appended.

New nodes: 0. New Mathlib leaves: 0. The item's statement, stmt_deps, source, created record and blueprint ancestry are unchanged. Its existing blueprint.same_as is confirmed as [].

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and normalized augmentation / comparison / transport terminology, including CategoryTheory and SixFunctors. The hits concern Koszul or Cartan--Eilenberg augmentations, specialized cohomology, and adjunction mate identities. None states this arbitrary-four-category result with both prescribed-square hypotheses and all its conclusions. In particular, Adjunction.unit_app_comp_map_mate_app in SixFunctors/Etale/BaseChangeTheorems/SmoothProperLocallyConstant.lean assumes adjunctions and concerns mates, which this item does not. No project attachment is claimed.

## WANTED

None. The item is an agent-created categorical extraction, and its full elementary proof is supplied here. No external theorem is needed.

## Problems found and changes

The live item was unsplit with an empty proof. The sandbox initially had no node, report, citations or search log, so I copied the live item before editing. No statement defect or missing hypothesis was found. The parent lem-sf-cbc-direct-image-reduction-unit, Step 2, uses precisely this item with the specified constant-limit normalization; I read its statement and that step to verify the orientation of b, j, eta and rho.

The source blueprint fix-lem-exchanges.proof.md Step 5 is the compactification-independence context, not a verbatim source for the abstract categorical lemma. I retain that provenance and explicitly mark proof_origin.by = agent. The proof is the extracted direct-image normalization argument spelled out, not an attribution of these formulas to Stacks 0A07. The derived-limit theorem 0A07 belongs to the specialization and is not used or cited as a premise in the abstract proof. No SGA source is used. The inherited chapter/unit placement is retained, and no unit or chapter route is changed.

## Searches and Mathlib verdict

Whole-blueprint searches were made with tools/blueprint_refs.py for "normalized augmentation", "constant-object normalization", "augmentation", and "normalization". The specific phrases gave no match; broader hits concern geometric, coefficient, or simplicial augmentations, not this abstract result. The ancestor command confirms fix-lem-exchanges. Whole-DAG keyword searches and the inspected parent show this node is the dedicated categorical extraction, not a geometric theorem to be used as its own premise. No new node was proposed.

The fresh searches, all recorded verbatim in the node and searches.jsonl, comprise LeanSearch, two differently phrased LeanFinder searches, Loogle NatTrans.naturality, and three source greps. LeanSearch found CatCommSq.iso_hom_naturality / iso_inv_naturality and NatTrans.naturality; LeanFinder first found specialized Dold--Kan and augmented-simplicial constructions, then natural-isomorphism cancellation and naturality_1' / naturality_2'. Loogle found the basic naturality axiom and unrelated pullback/pushout constructions. These are ingredients, not an exact match or a single one-line specialization giving the whole statement from its two hypotheses.

I read Mathlib/CategoryTheory/NatTrans.lean:53-58 (components and defining naturality equation), NatIso.lean:61-66 (component inverse identities), and CatCommSq.lean:58-67 (the two naturality identities). This confirms that all operations used in the proof are instances of the given categorical definitions. The single-file NatIso grep had malformed filename fields because rg suppresses the filename for one file; I recorded that actual result and repeated the relevant search on the CategoryTheory directory, obtaining correct file-and-line hits. All seven searches completed successfully; none is reported unavailable or claimed to have run when it did not.

## Not duplicates

No new nodes, hence no new/existing pairs. Existing def-nagata-category is reused for category laws. No small cancellation, substitution, or naturality claim was made into a node.

## Unfinished work

No mathematical part remains. The mandatory dry run and push are performed after this report is written. No Lean was written and no compiler, Lake, or build was run. All worker writes are confined to this item's sandbox.

## Review by NU

I read the item, the chapter sec-smooth-purity and unit sk-prop-sf-cbc records, GOAL.md, the three-level route rules in SETUP.md, the current fix-lem-exchanges proof, and the parent direct-image-reduction-unit statement and Step 2. The item is an elementary tool for the direct-image ingredient, not a new assertion of base change. The supplied abstract statement agrees with the parent's use: b points from PL_U to L_VQ; j points from L Delta to the identity; rho uses b inverse after L_V(h). I kept every hypothesis and conclusion, including naturality and both unit equations. There are no new nodes needing a separate source comparison.

I opened def-nagata-category and checked its actual statement: it supplies identity and associativity laws and nothing about natural transformations or derived limits. Those laws are exactly what every step cites it for. Functorial preservation of composition is part of the given functors' ordinary categorical meaning. Naturality of b and h is a hypothesis written in the item's statement. I do not attribute those facts to the category definition, and no non-elementary theorem is smuggled into that citation. citations.json quotes the category-law sentence verbatim for every use.

Step 1 substitutes eta_V = L_V(i_V) j_V inverse and maps the assumed augmentation equation under L_V. I checked that all three terms end in L_V Q B_U F and start at PF. It uses associativity from def-nagata-category and the given functor law only.

Step 2 substitutes precisely the constant-object normalization, whose two sides both run from PF to L_V Q Delta_U F. The orientation is essential and is the same as the item's assumption. Its def-nagata-category citation supports only reassociation.

Step 3 uses b's defining naturality at the actual morphism i_U,F : Delta_U F -> B_U F. The resulting equation is L_V Q(i) b_Delta = b_B P L_U(i). Substitution followed by P's composition law gives the first asserted equality. This is a displayed calculation, not a claim that b is automatically compatible with an arbitrary augmentation. The cited category definition supports its reassociation.

Step 4 multiplies that equality by b_B inverse and uses its two-sided-inverse property and the category identity law. It does not cancel eta, i, or h. The second asserted equality follows, with no unmentioned invertibility hypothesis. Again the category citation says precisely the identity and associativity laws used.

Step 5 obtains inverse naturality by explicitly multiplying b's naturality at B_U(t) on the left and right by the specified inverse components. The intermediate maps have the domains given by PL_U and L_VQ. The only cancellation is b inverse against b. There is no new theorem hidden behind the word transport; the equation is displayed and obtained by two multiplications and reassociation.

Step 6 applies L_V to h's assumed naturality and substitutes the equation from Step 5. Its three displayed lines prove the exact requested naturality formula, and the previously checked source and target of rho make this the definition of a natural transformation. The definition node is cited only for associativity, not for a theorem of functor categories. Every step is shorter than 2000 characters and consists of substitutions or two- or three-line equations; none hides an independent lemma.

I checked delivery-errors B--E against the actual files. B: the existing statement is self-contained and its categorical notions are inline or use the existing definition; no new unsplit node, proof-in-statement, missing source tag, unverified leaf, or unrun search is introduced. C: the only cited node was read, its quoted sentence supports exactly the laws used, proof_deps is the union of uses, and neither the parent nor any downstream node is used as a premise. D: all of the mathematical work is in these steps; no clause is shifted into a renamed node. E: the naturality equations are evaluated at the correct morphisms and in the correct categories; b and j are the only inverses used; no limit, derived, abelian, or small-index theorem is invoked.

Small cases: when all functors and comparison isomorphisms are identities the hypotheses say h i_V = i_U and the result is exactly that equation, with rho = h. In abelian groups with identity functors and identity b,j,chi, taking i_U = i_V = multiplication by 2 and h = identity checks that eta need not be invertible. Taking i_U = i_V = 0 and h = 0 checks a noninvertible h as well. Empty categories, whenever the displayed functors exist, make the component assertions vacuous. Finally, on abelian groups with all data identity except b = minus identity, the augmentation equation holds but the constant normalization fails; rho = minus identity would not preserve the identity augmentation on Z. This checks why Step 2 needs the normalization rather than assuming it. No statement repair was required. The only corrected issue during preparation was the helper's single-file grep display, handled by the repeated directory search without changing the helper.
