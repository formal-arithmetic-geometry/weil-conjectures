# lem-trf-tor-flat-base-change

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-tor-flat-base-change.json`: split, five proof steps; no Mathlib match for the complete item after the recorded searches.
- `citations.json`: one verbatim statement extract for every node used in every step.
- `searches.jsonl`: seven actual msearch invocations; existing item searches are preserved in the node, with the seven new queries appended.
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves.

## Attachments

None. Searches of the read-only project's `WeilConjectures/` for the exact blueprint tag and for flat/Tor base-change descriptions found no declaration stating the item. Upstream master was searched as reference material only. The item's existing metadata carries no Lean declaration. Existing closed/free-resolution and Mathlib nodes are reused as dependencies, not claimed as new attachments.

## WANTED

None. All sources needed for the proof are available locally.

## Corrections and source precision

The statement is correct and unchanged; the tensor-product definition is added to its statement dependencies. The original source wording described Stacks 00M8 as applying verbatim. The literal 00M8 theorem changes the ring over which Tor is taken, whereas this item keeps R fixed and changes only its coefficient module. I corrected the source description and recorded `proof_origin.by = agent` for the adaptation, without substituting the different theorem. The proof keeps the same R-free resolution throughout; no flatness of A over R or B over R is assumed or used.

The inherited blueprint ancestor is `lem-trf-local-term-locality`, with the existing via chain through the monomial Tor-independence argument. I retained it, read its blueprint text and the curve-zero chapter/unit route (including the current main-20261015 unit), and identified the coefficient-change subargument in split_report.blueprint. This item is not the unit's key statement, so its realized fields are unchanged. Whole-blueprint searches for `Tor flat base change` and `00M8` gave no matching blueprint node. The Tor-localization neighbour is only a localization statement; it does not subsume arbitrary flat coefficient extensions and is not used circularly.

## Not duplicates

No new nodes. The existing flat-tensor exactness theorem and exact-functor homology theorem are cited directly. The general free-resolution short-exact-sequence theorem already provides the required resolution by specialization, so no existence node is introduced. Faithfully flat reflection of vanishing is proved by the three-term exactness test in the existing definition, rather than introducing another vanishing lemma.

## Review by Q38

I read Stacks algebra.tex Tag 00M8 (label lemma-flat-base-change-tor), the Tor definition and resolution-independence discussion in Tag 00LY (section-tor), Tag 00HD (lemma-flat), the faithful-flatness definition Tag 00HB (definition-flat), and homology.tex Tag 010N (lemma-exact-functor). For resolution existence I read the degreewise split free-resolution construction in algebra.tex Tag 065P (lemma-reverse-long-exact-seq-ext). There are no new nodes with separate sources to audit. Every cited DAG statement was opened and compared with the claim its step uses, and citations.json copies its actual statement rather than its proof.

Step 1 uses exactly the free resolutions supplied by lem-weil-pbc-free-resolution-ses-split and the resolution computation supplied by def-weil-pbc-tor-modules. The specialization is the genuinely short exact sequence 0 -> M -> M -> 0 -> 0 with identity on M. No finite generation or Noetherian assumption enters. The complexes computing Tor are unaugmented, so their term at -1 is zero, which is essential for n=0.

Step 2 uses the universal property, generating pure tensors and functorial tensor maps in def-weil-pbc-module-tensor-product. I wrote both maps, both inverse checks, the two balancing checks and their equality with the differentials. These are elementary identities; the step does not hide a base-change lemma.

Step 3 uses lem-weil-pbc-flat-tensor-exact, whose statement asserts preservation of arbitrary exact three-term module sequences and therefore also the short exact sequences needed here. It does not cite the injectivity definition of flatness as if that definition were already an exactness theorem. Clause (c) of lem-sp-exact-functor-preserves-homology explicitly gives the cycle/quotient-compatible comparison for any three-term complex. It applies in Mod_A and Mod_B without a boundedness requirement, degree by degree, and gives the formula [z] tensor b -> [z tensor b]. This avoids mistakenly applying the existing bounded-complex flat-cohomology lemma to an infinite resolution.

Step 4 uses the second-variable functoriality in def-weil-pbc-tor-modules and generation by tensors from def-weil-pbc-module-tensor-product. I computed the map on a representative sum of tensors and compared it with the coefficient map induced by A -> B, followed by multiplication by b. Thus the argument proves invertibility of the stated canonical B-linear comparison, including its direction; it does not merely produce some isomorphism.

Step 5 uses exactly the reflection of exactness in def-weil-pbc-faithfully-flat-ring-map and the elementary tensor-switch map from the tensor universal property. Applying the definition to 0 -> T -> 0 proves T=0. Faithful flatness is used only in this consequence.

I tested n=0, where the comparison is ordinary tensor reassociation, M=0, the identity A=B, and the flat zero-algebra case B=0. The latter correctly gives no vanishing descent unless A is also zero, because faithful flatness then fails otherwise. I also checked R=Z, A=Z/2, B=A with M=Z/2: A is not R-flat and Tor_1 is nonzero, but the asserted comparison is the identity, confirming that the proof has not accidentally imposed R-flatness. Dropping A-flatness of B fails already for R=A=Z, B=Z/2, M=Z/2 in degree one, which validates where flat exactness is used.

The review against delivery-errors B--E found no statement dispute, hidden hypothesis, new definition, duplicate, restated clause, cycle or uncited non-elementary ingredient. All five steps are shorter than 2000 characters. The sources use no SGA route. JSON, dependency unions and quotation agreement were checked; the required server dry run follows. No Lean was written or compiled, and no direct git command or live-project write was made.

## Unfinished work

None in the mathematical split. Delivery is complete only after the required dry run and push below.
