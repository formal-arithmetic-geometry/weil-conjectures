# Worker report: sk-thm-picard-cech

## Files written

- `dag/nodes/sec-picard-framework/sk-thm-picard-cech.json`: statement; split using existing nodes; Mathlib searches found definitions and general infrastructure, not this spectral-sequence theorem.
- `dag/units/sk-thm-picard-cech.json`: only `realized` and `realized_by`, binding the statement and all five recorded unit paragraphs to the item and the existing comparison nodes.
- `citations.json`: twelve verbatim statement quotations, one for every node/step citation.

New nodes: 0. New Mathlib leaves: 0. No Lean files or compiler/build tools used. Repository and launcher files were read only.

## Attachments

None. This is a split, not a renewal of the attachment rejected by the second reader. The present read clone contains a later, longer implementation of `CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence` (Cech.lean:289), but I make no claim that its transitive dependencies are closed. The mathematical proof below uses the existing DAG statements as dependencies.

## Literature

No WANTED documents. I read the current main-20261015 statement at `literature/blueprint/main-20261015/blueprint/sec-picard-framework/sk-thm-picard-cech/_section.md` (order 715). This file has the statement but no proof. I read the full recorded unit and its original proof in `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-cech/_section.md`, and the general spectral-sequence statement and proof at `literature/blueprint/master/blueprint/sec-abelian-varieties/sk-prop-av-pqf-finite/thm-sp-double-complex-spectral-sequences.md`.

The Stacks sources read were `sites.tex`, Tag 00VI (`remark-no-big-sites`) and Tag 00VH (`definition-site`); `sites-cohomology.tex`, Tag 03F6 (`lemma-injective-abelian-sheaf-injective-presheaf`), Tag 03AW (`lemma-injective-trivial-cech`), and Tag 03AZ (`lemma-cech-spectral-sequence`); and `injectives.tex`, Tag 01DP (`theorem-sheaves-injectives`). Stacks proves 03AZ through the Grothendieck spectral sequence. This delivery preserves the unit's equivalent injective-resolution double-complex route and accordingly records agent proof origin, rather than attributing that route verbatim to Stacks. No SGA source is used.

## Corrections and scope

The statement is retained verbatim. Its site/Cech/abutment definitions now appear in `stmt_deps`. The small-site convention is supplied by `def-weil-pbc-sites-and-cohomology`, and is exactly the source convention of 00VI: this does not assert the theorem for an arbitrary large site or an unrelated coefficient universe. In the column/total lemmas the Ext groups are computed by the specified injective resolution in the common universe, as the definition of cohomology over an object stipulates. No extra acyclicity hypothesis on F or on its intersections is added.

The old proof chose a resolution on C/X and then used it as though its terms were sheaves on C. Those expressions do not have the stated domains without introducing restriction first. I corrected the choice to a resolution of F on C, as in Stacks; the double-complex route and theorem do not change. Restriction preserving injectives and the exactness of its left adjoint are unnecessary: cohomology over V is already computed by evaluation of this resolution. The column lemma explicitly supplies an isomorphism of horizontal complexes, including their differentials, so the proof does not infer compatibility from termwise isomorphisms alone.

The old citation to sk-def-groth-ss did not by itself supply explicit E1/E2 page formulas. I now use the existing general double-complex theorem for those formulas, and retain sk-def-groth-ss for the unit's notion of abutment. The optional row-zero collapse of the unit is spelled out after the claimed spectral sequence has been proved.

## Searches and reuse

DAG searches by tags 03F6/03AW/03AZ and by Cech, double complex, and enough injectives found the existing comparison nodes. Whole-blueprint searches `python3 tools/blueprint_refs.py search cech` and `search Čech-to-derived`, and `ancestor sk-thm-picard-cech`, identified `lem-sc-cech-spectral` as the detailed same statement (with the small-site convention already recorded there). It is in `blueprint.same_as`, not introduced as a new node or used to replace the proof of the item.

The project Lean search for the item tag, theorem name, and Cech-to-derived terms found the theorem and the specified double-complex infrastructure. I read the theorem signature/body and the current Mathlib Cech functor and cohomology-presheaf definitions. The logged Mathlib searches were two LeanFinder phrasings, LeanSearch, two Loogle queries, and two regex searches; all exact queries and actual results are in the node and searches.jsonl. LeanFinder returned Mayer-Vietoris/cohomology-presheaf definitions and injective-resolution infrastructure, LeanSearch returned definitions and spectral objects, and the regex searches found no Cech spectral-sequence theorem. The first Loogle query had an unknown identifier and is recorded as an invalid query, not evidence of absence; the second substring query ran successfully with no hits. This is not a Mathlib-leaf claim.

## Not duplicates

No new nodes, hence no new/existing same-tag pairs. All construction, page, total, and injective-existence facts are reused. In particular no new node is a clause of this theorem, and none restates lem-sc-cech-spectral.

## Tool use

`thm-sp-double-complex-spectral-sequences` is the generic first-quadrant spectral-sequence tool explicitly required by the unit's Step 1. Its statement supplies page formulas and convergence. It belongs to another unit and is declared in `split_report.tool_uses`; it does not replace any unit step. The remaining comparison nodes are in this unit; the enough-injectives node is a Mathlib leaf and the other external notions are definitions.

## Review by NV

I compared all seven steps with their sources and opened the statement of every cited node. There are no new nodes requiring a separate source audit.

1. I checked that the enough-injectives statement applies to abelian sheaves on a small site, not only etale sheaves. It explicitly supplies an abelian category with enough injectives. The injective-resolution definition names the object and resolution, and the cohomology definition explicitly says H^q(V,F) is the cohomology of I(V). The selected resolution is on C. The common-universe convention is the small-site convention read in 00VI; no use is made of the unsupported arbitrary-large-site version.
2. I checked the specified double-complex construction: it accepts a family without a covering hypothesis, has outer Cech degree and inner resolution degree, and states that the differentials commute. The total-complex definition states d_I+(-1)^p d_II and finite diagonals. The fibre products in the item's hypotheses give every required finite wide pullback: the empty diagram over X has limit X and the nonempty ones are iterated fibre products. This is about products in Over X, so no final object of C is assumed. Expanding that construction and the finite total is elementary.
3. I read the first-filtration clause of the general double-complex theorem and its convergence clause. They give exactly vertical cohomology on E1, horizontal induced d1, horizontal cohomology on E2, and the finite image-filtration abutment. The proof does not cite a definition for this existence result.
4. I read the entire column-comparison statement. It says naturally isomorphic as complexes with the horizontal differential equal to the Cech differential; that is the precise compatibility the step needs. The Cech-definition node supplies the equality between Cech cohomology and cohomology of the Cech complex. The common-universe/resolution conventions and fibre products were checked above; the column comparison needs no covering or intersection-acyclicity assumption.
5. I read the total-comparison statement. Unlike the column statement, it explicitly assumes that the sieve generated by the family is covering, exactly the item's hypothesis. It is about the same specified resolution and double complex and gives the isomorphism for every n. I take only that assertion, not a construction hidden in its proof; the discussion of row acyclicity identifies its source role. The preceding theorem and this comparison are strictly smaller existing dependencies, not renamed clauses created for this delivery.
6. I checked the quoted abutment definition, including its endpoint bounds and the successive-quotient isomorphisms. Sending each subgroup of the total-cohomology filtration through theta preserves inclusions, endpoints and quotients. Writing that out gives the asserted abutment without silently claiming an extra compatibility theorem. This is an elementary change along an isomorphism, applied to the already cited first-filtration abutment.
7. I checked the optional collapse separately. Degree-zero cohomology is F by the cited site/cohomology definition. For r>=2, outgoing differentials from q=0 leave the first quadrant, and incoming ones have q=r-1>0 and therefore zero source. All other graded pieces vanish; the finite abutment filtration consequently has only its degree-n quotient nonzero. This proves the row-zero edge isomorphism claimed by the original unit without adding it to the theorem's hypotheses.

I also checked the small cases: F=0 gives zero pages and abutment; a singleton identity covering is the augmented constant Cech complex and causes no higher Cech-degree anomaly; repeated cover members are allowed because tuples, not strictly increasing indices, are used; an empty family is admissible only when its empty sieve covers X, in which case every abelian sheaf (and every term of I) has zero sections there and the asserted total comparison gives zero cohomology. Arbitrary set-indexed products are used, with their compatibility included in the column-comparison statement; no finiteness of the cover is smuggled in. No non-elementary step exceeds 2000 characters (the longest is 851), and no hidden standalone lemma is left inside a long step.

Against delivery-errors B--E: the item carries statement/definition dependencies and exact blueprint references; there are no unsplit new nodes with proof sketches, no fabricated searches, no source-tag-based definition of an object, and no Mathlib match to overstate. Each non-elementary argument is the statement of a cited dependency. The two complex comparisons have separate hypotheses and are not interchanged. The final filtration calculation and optional collapse are explicit. Node/unit metadata outside the permitted fields are preserved. No unresolved mathematical work remains for this one-level split; the existing open dependency nodes remain their own work items.

## Validation

The required server dry run and delivery are performed after this report is written; their final output is authoritative. citations.json was checked locally for exact substring inclusion against the current dependency statements. No server checker is run locally.
