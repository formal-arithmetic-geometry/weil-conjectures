# Stage-1 worker report

## Files written
- dag/nodes/sec-proper-base-change/lem-weil-pbc-descend-open-immersion-qcqs.json: item split; no Mathlib match for the full descent assertion.
- citations.json: one verbatim statement quotation for every step citation.

## Attachments
None for the item. Searches in WeilConjectures by the blueprint id and descent/open-immersion notions found no declaration stating the whole item. The existing recognition node lem-weil-pbc-radicial-etale-open is already attached to AlgebraicGeometry.IsOpenImmersion.of_etale_of_universallyInjective, whose proof at Gluing.lean:60–67 was read.

## WANTED
None.

## Corrections and route
The statement was retained, including arbitrary qcqs models, local finite presentation and the all-later conclusion. The empty imported proof has been replaced by six steps. The proof is marked agent-written: Limits 0EUU uses 07RP, the open image, and isomorphism descent, whereas this split uses the existing 07RP and 07RQ nodes and Etale 025G. This changes only the auxiliary node proof, not the chapter or unit route. The three levels of SETUP permit this below-node choice. The source includes 07RQ and 025G; no new statement packages a clause of the item.

The two descent nodes are generic tools in sk-thm-p1, declared in split_report.tool_uses. Neither replaces any proper-base-change unit step. All other cross-unit inputs are definitions, Mathlib leaves or the already closed recognition node.

## Not duplicates
No new nodes. Whole-DAG and whole-blueprint searches for open immersion, monomorphism and 025G were read. The existing radicial recognition theorem and its definition equivalences suffice: a proposed monomorphism-to-universal-injectivity leaf was unnecessary and was not created. Its exploratory Mathlib searches remain only in searches.jsonl, not attributed to a new node.

## Review by NS
I read Limits Situation 081D and lemmas 0EUU, 07RP and 07RQ, Morphisms 01S4, the base-change-etale and open-immersion-etale lemmas, and Etale 025G in the local Stacks sources. I read the chapter and sk-thm-properbasechange unit records and the nearest blueprint ancestor's finiteness proof. The six steps concern its classical constructibility auxiliary limit argument, not a change to its coefficient categories or base-change morphism.

Step 1 uses the full statements of lem-weil-pbc-open-immersion-etale and lem-weil-pbc-open-immersion-monomorphism. They give precisely étaleness and categorical cancellation for the limit morphism. Step 2 uses the affine basis statement to cover each inverse image of an affine target open, and the affine-pair finite-presentation statement to obtain an explicit polynomial quotient. The images of its variables are finite generators, meeting exactly def-weil-finite-type-morphism. This step is not labelled elementary because the affine-pair theorem is substantive.

Step 3 uses the statements, not proofs, of lem-weil-pbc-descend-etale and lem-weil-pbc-descend-monomorphism. I checked each demands only qcqs S at the initial index, qcqs X and Y, affine transitions, and respectively local finite presentation and local finite type. All hold here, with monicity and étaleness at the limit established in step 1. There is no affineness or separatedness assumption on X or Y hidden in their use.

Step 4 cites étale scheme base change, whose statement is the required projection assertion. Monicity after base change and the identification of repeated base changes are written out from def-pc-fibre-product's universal property; no uncited descent theorem is concealed. A common upper bound of two indices exists by directedness and remains above i0. Step 5 uses the injective-field-points equivalence explicitly stated in def-weil-radicial-morphism, not merely the word radicial. Monicity gives that injectivity by cancellation. The statement of lem-weil-pbc-radicial-etale-open then supplies exactly an open immersion, without supplementary hypotheses. Step 6 uses the statement of open-immersion base-change stability and the same explicit pullback identification to obtain every later stage. citations.json contains the statements I checked verbatim.

I checked delivery-errors B–E: no new nodes or unsupported new notions, source labels and tags specified, no relabelled child, all non-elementary inputs cited, all cited hypotheses verified, no use of affine intersections or flat transition maps, no statement weakening. The empty-source and empty-limit cases cause no exception: property descent applies to them, a common stage still exists because i0 is present, and the finite-generator argument includes n=0. Constant systems and a one-element index set reduce to recognition of the given open immersion. No surjectivity of transitions or of the initial morphism is used.

## Unfinished work
None in this one-level split. The dry run is the final check; a fresh reader will deliver.

## Second reading by NS

Item statement: checked against Limits 0EUU, `lemma-descend-open-immersion`, and Situation 081D, `situation-descent-property`; PASS. The imported all-stages-qcqs hypothesis is retained, as are qcqs models and local finite presentation; the source conclusion at one stage implies the all-later conclusion by open-immersion base change. No statement correction is needed.

Step 1: read the statements of lem-weil-pbc-open-immersion-etale and lem-weil-pbc-open-immersion-monomorphism against Morphisms `lemma-open-immersion-etale` and Schemes `lemma-immersions-monomorphisms`; PASS, both apply to the given limit morphism without extra hypotheses.
Step 2: read lem-weil-pbc-affine-opens-basis against Schemes `lemma-basis-affine-opens`, and lem-weil-pbc-lfp-affine-opens-finite-presentation against Morphisms 01TQ, `lemma-locally-finite-presentation-characterize`, clause (2); PASS. Affine neighbourhoods are taken inside the open inverse image, not affine intersections; polynomial generators give exactly def-weil-finite-type-morphism's cover condition, including zero generators and the empty source.
Step 3: read both descent-node statements against Limits 07RP, `lemma-descend-etale`, and 07RQ, `lemma-descend-monomorphism`, with Situation 081D open; PASS. Each original model and base is qcqs, transitions are affine, and the distinct finite-presentation/finite-type hypotheses are supplied by the item/step 2. Their statements supply the two indices independently; neither proof is used as an interface.
Step 4: read lem-weil-pbc-etale-scheme-base-change against Morphisms 02GO, `lemma-base-change-etale`, and def-pc-fibre-product's universal property; REPAIRED. Explicit mutually inverse compatible-pair formulas now give the two pullback identifications; monicity after pullback is proved by cancellation and uniqueness. Directedness supplies one upper bound, with no surjectivity assumption.
Step 5: read def-weil-radicial-morphism's four-way equivalence against Morphisms 01S4, `lemma-universally-injective`, and lem-weil-pbc-radicial-etale-open against Etale 025G, `theorem-etale-radicial-open`; PASS. Cancellation on every field's points gives radiciality, and étaleness gives the open immersion. Also read the attached closed declaration AlgebraicGeometry.IsOpenImmersion.of_etale_of_universallyInjective at Gluing.lean:60–67; it has precisely the required hypotheses and no local sorry, consistent with the recorded closed audit.
Step 6: read lem-weil-pbc-open-immersion-base-change against Schemes 01JY, `lemma-base-change-immersion`, and def-pc-fibre-product; REPAIRED. Replaced the reference to “the same” identification with the explicit forward and inverse compatible-pair formulas, and applied stability to the resulting projection for arbitrary later j.
New nodes: none; B1–B7 and new-node Mathlib searches have no new node to check. The sandbox contains only the item node; all twelve proof dependencies already exist and their statements were opened. No clause has been moved into a new node and no new Mathlib leaf is asserted.

Small cases: empty source and empty limit remain covered by the descent statements, including eventual disappearance where needed; for a singleton index or constant system the argument reduces to recognition of the original open immersion; polynomial presentations with n=0 are generated by the empty tuple. No nonempty scheme, nonzero ring, affine model, separated model, or flat/surjective transition is assumed.

Changes: expanded the pullback identifications in steps 4 and 6 to remove E5 shorthand. Removed split_report.tool_uses: the report requests reviewer recognition of lem-weil-pbc-descend-etale and lem-weil-pbc-descend-monomorphism as generic tools, for the reasons in the first worker's route section; accepted tool-use fields belong to the maintainer. The first worker's statement, remaining proof steps, searches, and Review by NS are retained. citations.json was checked against every cited statement verbatim; changed steps use the same citations, so no quotation changed.
