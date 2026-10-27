# Worker report: lem-sfb-field-extension-immersion-koszul-points

Group Q113, direct stage-1 delivery, 2026-10-24.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-field-extension-immersion-koszul-points.json: statement item, now split into seven proof steps. No exact Mathlib match; all supplied hypotheses and the statement are unchanged.
- citations.json: 19 entries, one verbatim statement excerpt for every node cited by every proof step.
- report.md: this report. searches.jsonl is the search command's own record.

New nodes: 0. New Mathlib leaves: 0. Every prerequisite already exists in the DAG.

## Attachments

None. Searches for the item's blueprint tag and for field/Koszul/immersion declarations under lean/WeilConjectures found no declaration proving its pointwise equivalence. The existing Koszul-regular immersion modules establish perfection or Ext/duality consequences of a supplied regular presentation, rather than descent of the presentation. In particular, KoszulRegularImmersionExtPullback.lean assumes hregular; it cannot attach this item.

## WANTED

None. All mathematical sources used are present in literature/stacks-project/.

## Findings and route

The item had no proof. Its mathematical statement is correct as supplied. The main point not to omit is that an arbitrarily selected open regular neighbourhood upstairs need not surject onto the original ambient affine open. Take its open image first and then choose a principal open inside that image. Only the resulting restricted affine map is used as a faithfully flat cover.

I read descent.tex Tag 0694 (lemma-descending-property-regular-immersion) and more-morphisms.tex Tag 06B8 (lemma-base-change-lci-fibres), including the latter's use of the flat universally open residue-field map. I expanded the neighbourhood descent argument using the algebra statement of more-algebra.tex Tag 068N (lemma-flat-descent-regular-ideal), already represented by lem-sfb-koszul-ideal-faithfully-flat-descent. The proof is marked agent-written because the explicit shrinking argument is assembled here, rather than copied as a proof of a separate pointwise lemma from Stacks.

The chapter and unit records were read. The latest blueprint direct-images proof, paragraph (3), is the ancestor route; this item is a supporting input deep in its alteration/lci chain, not the unit key statement. No unit realization or chapter record was changed. The existing blueprint.from.node is null and the ancestor command also reports None; that inherited provenance was preserved. Its detailed from.place already specifies the relevant residue-field step. Whole-blueprint searches for 0694, faithfully flat Koszul, and field-extension immersion found no exact blueprint statement. same_as remains [].

## Mathlib searches

The item's inherited searches are retained. Six additional searches were run through the required msearch.py command and recorded verbatim from searches.jsonl: LeanSearch; two LeanFinder phrasings; two Loogle queries; and grep in AlgebraicGeometry. The first Loogle query used a guessed identifier KoszulComplex.IsRegular, which the service reported as unknown. It is recorded as an invalid query, not evidence of absence. The follow-up quoted Koszul query returned zero hits. Other hits include ordinary immersion base-change stability, smooth ring-map base change, and regular-sequence ascent. I read Mathlib/RingTheory/Regular/Flat.lean and Mathlib/AlgebraicGeometry/Morphisms/Immersion.lean: these do not assert descent of the Koszul-regular immersion locus at a chosen lifted point. No leaf claim is made. No service outage was represented as a negative result.

## Not duplicates

No new nodes were created. Existing affine Koszul-regularity, faithfully flat ideal descent, flat ascent, universally open field projection, and scheme/ring localization nodes are cited directly. In particular, the already-present lem-sfb-koszul-immersion-flat-ascent-etale-descent is used only for its flat-ascent clause: its descent clause concerns etale covers and would not justify an arbitrary field extension. The algebraic ideal-descent node supplies the stronger descent needed here. No claim has been moved into a restatement node.

## Review by Q113

I checked this split against delivery-errors.md B--E with the node statements and source paragraphs open. There are no new statements to source or test. The statement is unchanged, every object in the proof is introduced, and the seven proof steps are all below 900 characters each. The non-elementary arguments cite actual statements; no step is marked elementary merely because it is a standard theorem.

Step 1 uses def-weil-closed-immersion for the factorization through an open target and the affine quotient description; lem-weil-pbc-affine-opens-basis for the affine target chart; and the first clause of lem-weil-pbc-quotient-base-change-closed-immersion-ideal for the pulled-back ideal IB. The statements give exactly these facts. The only extra reasoning is the subspace-topology identity N=Z_U intersect O, which explains why shrinking a source neighbourhood can be effected by shrinking the ambient target when the immersion is closed. This does not assume the entire original immersion is closed in P.

Step 2 uses lem-pc-field-extension-flat and lem-weil-pbc-flat-morphism-base-change to show the projection q is flat. The first clause of lem-sfb-koszul-immersion-flat-ascent-etale-descent then applies to the chosen regular presentation. The source and target opens remain open by lem-weil-pbc-open-immersion-base-change. I checked that z_K belongs to the inverse image of the chosen neighbourhood, and that arbitrary extensions, including infinite and inseparable ones, satisfy the flatness premise. No etale descent statement is used.

Step 3 uses the affine-neighbourhood equivalence of lem-sfb-koszul-closed-immersion-affine-criterion after the local ambient reduction of step 1. Its statement gives a finite Koszul-regular generating sequence on an affine W. The quotient base-change node identifies the particular ideal with IB, rather than just some ideal cutting out an isomorphic point set. This is also what divisors.tex Tag 063G and schemes.tex Tag 01JU say. The chosen W lies inside U_K, which is necessary to obtain the map A to B.

Step 4 uses lem-sc-scheme-over-field-universally-open with base field k, X=Spec K, S=P; the symmetry of the fibre product only interchanges projections. Its statement explicitly says the projection sends every open to an open. Thus q(W) is open and contains p. The basic-open basis node provides h outside the prime p with D(h) contained in q(W); the affine-open section localization node identifies the principal opens with Spec A_h and Spec B_phi(h). I wrote the prime-comap calculation establishing the inverse-image equality. There is no finite-presentation assumption on Spec K to Spec k at this step.

Step 5 proves surjectivity on spectra point by point, using the containment D(h) subset q(W). The flat affine criterion applies directly to the affine opens D_W(phi(h)) of P_K and D_U(h) of P, since q is flat and maps the first into the second. It says exactly that the induced A_h to B_phi(h) map is flat. The flat-surjective-spectrum node then gives faithful flatness; this avoids wrongly claiming that W to U was already surjective. The sources are morphisms.tex Tag 01U5 and algebra.tex Tag 00HQ, read in full at their statements and proofs.

Step 6 uses localization flatness and the algebraic Koszul flat-ascent node to keep the sequence regular after localizing B. It then applies lem-sfb-koszul-ideal-faithfully-flat-descent to A'=A_h, B'=B_phi(h), J=IA'. I checked every premise in that statement: a faithfully flat map of commutative rings; an actual extended ideal JB'=IB'; and regular generators at every prime containing it. The last condition holds with localizing element 1 because the generators are global on B'. The prime pA' exists since h is outside p and contains J since p is the image of a source point. This is the statement of Tag 068N, not a hidden use of that node's proof.

Step 7 uses the same quotient base-change clause for the final ideal and the affine regularity criterion for the final neighbourhood D(t) of p. Since this is an open of D(h), it is an open of P. Its preimage in Z contains z and gives the required near-z statement. Combining this with step 2 proves the two directions at the originally specified lift. The proof does not appeal to a different lift or confuse a stalk property with an open-neighbourhood property.

The small cases checked were K=k; a nontrivial purely inseparable extension; a transcendental extension; an open immersion (I=0 and the empty sequence); an empty Z_K (vacuous universal quantifier); and a nonregular closed ideal such as (x^2,xy) in k[x,y] at (x,y). In the last case, a regular lifted neighbourhood would force one downstairs by the same faithful-flat descent, so the proof does not silently promote every immersion to a regular one. The given local finite-type hypothesis is retained, although the proof needs no Noetherian argument. No global quasi-compactness, separation, finiteness of degree or separability was added. We never assume an intersection of affine opens is affine: affineness of the shrinking is supplied by principal-open localization.

The split_report.tool_uses entries declare the generic foundational tools from other units, for the maintainer to judge; the existing same-unit Koszul-ideal and affine-criterion nodes are used directly. These applications do not replace the unit route. No SGA source is cited. I corrected the initially tempting inference that an arbitrary regular open upstairs is a cover of the whole original affine chart by explicitly inserting the open-image/principal-open restriction; I also replaced the guessed Loogle identifier by a successful quoted search. There is no remaining mathematical gap or uncompleted subtask in the split.

## Unfinished work and verification

No mathematical work remains for this stage-1 item. Remote srvcheck review_split returned PASS (0 new nodes). The required deliver.py --no-push completed with OK (not pushed) at dade20ddc11, with server preflight passed. All 19 citation excerpts were separately checked against the current node statements, and the item statement is byte-for-byte unchanged. This report update records those completed checks; the final delivery invocation validates the submitted content again.
