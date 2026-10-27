# Stage-1 report: lem-sfb-unramified-geometric-equivalence-relation

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-unramified-geometric-equivalence-relation.json: item split into five proof steps; no Mathlib declaration states the whole criterion.
- citations.json: ten verbatim statement quotations, one for each step/node citation.
- report.md and searches.jsonl: report and actual logged searches. No new nodes; no new Mathlib leaves.

## Attachments

None. I searched the full live lean/WeilConjectures tree for the blueprint tag, equivalence-relation names and words, and unramified/monomorphism combinations. No project declaration gives every clause. The field-point and unramified morphism inputs already occur as Mathlib leaves in the DAG; they are citations, not attachments for this item.

## Wanted literature

None. All sources used are available locally.

## Corrections and route

No statement correction and no STATEMENT-DISPUTED issue. The imported statement is the etale specialization of Stacks Tag 0DT7 (groupoids.tex, lemma-etale-equivalence-relation). The hypothesis that j identifies R(K) with an equivalence relation includes injectivity, not merely that its image is an equivalence relation. This interpretation is essential to the diagonal argument and is the source's interpretation. The source uses the opposite ordering of the composable-arrow fibre product; the item consistently uses t(r)=s(r') and output (s(r),t(r')), so its convention is equivalent.

I replaced the empty proof with the source's diagonal proof and expanded its last sentence into explicit reflexivity, symmetry and transitivity witnesses. I retained all existing metadata and historical searches. I added only actually logged searches, inspected their recorded results, and made a second search formulation (unramified morphisms injective on algebraically closed points) and a second Loogle pattern. Loogle's first query did not recognize IsEtale; this is recorded as an unusable result, not evidence of absence. The second query returned zero hits. LeanFinder/LeanSearch returned property and monomorphism instances, not the full criterion; the source grep found the open-diagonal instance but no equivalence-relation theorem.

I read the chapter and unit records and the current latest blueprint files for sk-thm-sf-ctf-stability and det-thm-sf-ctf-stability-direct-images. The latter is stored as sk-thm-sf-ctf-stability-direct-images.proof.md; its current part (3) is the compactification/direct-image argument. The long alteration/coarse-space description in blueprint.from.place is inherited provenance of the supporting lemma chain, not a claim that the current blueprint explicitly states this elementary scheme criterion. I searched the complete current blueprint for the relation, tag and unramified words; none states this item. The ancestor command returns None for this inherited supporting chain. I preserve that provenance and its precise existing place, and keep same_as empty. The proof uses only existing definitions and Mathlib leaves, so no off-unit tool approval is needed and no chapter/unit route is replaced. This item is not the key unit statement, so no unit record is changed.

## Not duplicates

No new nodes. The existing lem-sfb-scheme-unramified-composition-cancellation supplies exactly the permanence assertion needed at the start. The existing def-weil-unramified-morphism already includes the open-diagonal characterization; no new diagonal lemma is needed. The existing field-point classification and algebraic-closure nodes cover the geometric lift of any ordinary point. Surjectivity of an open immersion implying isomorphism is immediate from def-weil-open-immersion. Diagonal isomorphism implying monomorphism is proved explicitly by the fibre-product universal property rather than made into a new node.

## Review by Q63

I read Stacks groupoids.tex Tag 0DT7 in full, including its proof. I also read morphisms.tex Tags 02GG (lemma-unramified-permanence) and 02GE (lemma-diagonal-unramified-morphism), and the field-point discussion and lemma-characterize-points, Tag 01J9, in schemes.tex. There are no new nodes with further source obligations. I read the statement of each node cited below, not merely its proof or title, and copied the relevant statements without changing their TeX into citations.json.

Step 1 uses def-weil-etale-morphism specifically for its unramified condition. The statement of lem-sfb-scheme-unramified-composition-cancellation explicitly says that an unramified composite implies the first factor is unramified with no condition on the second. I apply it to j followed by p1, whose composite is s; no separatedness or finite-type condition on the projection is silently used. I also checked its Mathlib source at FormallyUnramified.lean:111 and FiniteType.lean:72. The statement of def-weil-unramified-morphism explicitly gives an open diagonal, as required for d. The stated universal property in def-pc-fibre-product supplies B, P and d.

Step 2 uses only that fibre-product universal property and the item's hypothesis: the projections of q have equal composites with j, hence injectivity on the same algebraically closed field and the same S-structure gives a=b, and the unique pair map is d composed with a. No assertion that all geometric points detect equality of arbitrary scheme maps is used.

Step 3 uses the existence sentence of def-weil-algebraic-closure and the full bijection stated in lem-weil-pbc-morphism-from-spec-field, including that its inverse maps a pair (z, kappa(z) to K) to a morphism with underlying image z. I read the corresponding source discussion and checked SpecToEquivOfField and fromSpecResidueField_apply at ResidueField.lean:346 and :272. Composing this geometric point with P to S gives the exact field-over-S required in the hypothesis. Thus every ordinary point of P is in the diagonal image. The statement of def-weil-open-immersion identifies the source with the open subscheme on its image, so image equal to P makes d an isomorphism with its full scheme structure, not just a homeomorphism. These are a few immediate deductions from the cited statements; this step is marked elementary.

Step 4 checks monomorphism for arbitrary schemes T, not only reduced schemes or S-schemes. The cited fibre-product definition gives h=(a,b); applying the inverse of d and its two projection identities gives a=b. This also proves cancellation on infinitesimal test schemes without imposing reducedness.

Step 5 uses the stipulated identities for e,i,c and the fibre-product definition. For transitivity I checked the order t(r)=s(r') against the item's chosen fibre product, and that the image of c(r,r') is (s(r),t(r')). Reflexivity and symmetry are witnessed by e(x) and i(r). The witnesses are S-morphisms because their composites with j have the displayed S-compatible coordinates. No groupoid associativity or inverse axioms beyond the given coordinate identities are needed.

Against delivery-errors B--E: every used non-elementary input is a named existing node with a statement quote; I introduce no disguised clause-node, no duplicate, and no unsearched new node. All proof steps are shorter than 2000 characters (500, 407, 597, 333, 737). I tested the empty scheme case (e forces R empty when U is empty), diagonal equality relation R=U (j is the diagonal of an etale identity presentation), the full relation on an etale U/S, and nonreduced arbitrary T in the cancellation step. Multiple arrows over one geometric pair are excluded by the explicit injectivity hypothesis; merely assuming that the image is an equivalence relation would fail, for example for a nontrivial finite constant group over an algebraically closed field with U a point. The imported wording excludes that counterexample, so no statement repair is necessary.

## What remains

No mathematical work remains for this stage-1 split. No Lean was written, no compiler or Lake command was run, and only the assigned sandbox was written. The server review_split check passed with zero new nodes; it notes only the inherited unit has no realization recorded yet. The first dry run required the algebraic-closure quote to be at least 40 characters; I replaced it by the entire verbatim statement. The required final delivery dry run and push follow this report.
