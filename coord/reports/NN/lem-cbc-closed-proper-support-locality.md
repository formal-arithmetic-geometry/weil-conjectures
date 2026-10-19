# Worker report

## Files written

- `dag/nodes/sec-smooth-purity/lem-cbc-closed-proper-support-locality.json`: item, split into four steps.
- `dag/nodes/sec-smooth-purity/lem-weil-pbc-proper-morphism-fpqc-descent.json`: new statement-only generic lemma, Stacks 02L1; Mathlib searches found no exact covering-family match. No new Mathlib leaves. Existing `lem-weil-pbc-lft-base-change` is reused.
- `citations.json`: one verbatim quotation for every citation of every proof step.

## Attachments

None. Searches of `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the item id and proper-support notions found no declaration stating the item. The upstream master is reference material, not proof evidence.

## Literature wanted

None.

## Corrections and unfinished work

The imported statement agrees with Stacks 0CYP and with the etale-cover specialization of 0F4J; it was not changed. The initial draft incorrectly asserted that arbitrary base change preserves reducedness. I removed that inference: the pullback of the reduced closed structure is merely a closed structure on the inverse-image subset, and 0CYL supplies independence of the scheme structure. For example, a purely inseparable field extension of a field tensored with itself can have nilpotents, so reducedness cannot be presumed.

An initial proposed support-descent helper merely restated clause (2). It was removed under D1/D2. Its replacement is ordinary proper-morphism fpqc descent (02L1), whose statement has no closed-subset or local-finite-type ambient hypotheses; the item itself carries the passage from closed support to a scheme morphism. A proposed local-finite-type base-change node was also removed when the duplicate check identified the existing exact leaf `lem-weil-pbc-lft-base-change`.

The new 02L1 node is deliberately unsplit, with no proof sketch or proof dependencies. There is no further unfinished work on the item's one-level split. No Lean was written and no compiler, Lake, or build command was run. Delivery was dry-run only; nothing was pushed.

## Review by NN

I read coherent.tex at `lemma-base-change-closed-proper-over-base` (0CYP), including its scheme-theoretic inverse-image proof, and descent.tex at `lemma-descending-property-proper-over-base` (0F4J), including its appeal to 0CYL and `lemma-descending-property-proper` (02L1). I also read the latter's statement and proof: it is fpqc locality of ordinary proper morphisms, obtained from universally closed, separated and finite-type descent. The new generic node states its descent direction for an arbitrary covering family, with no noetherian or finiteness assumptions on the base. This agrees with 02L1. The chapter, unit and ancestor blueprint were read; this realizes the refinement-comparison requirement for the proper-support sheaf, without changing the coefficient categories or the unit route.

Step 1 uses the statement of `lem-weil-pbc-reduced-induced-closed-subscheme` (2) to identify the image of the reduced structure with C; `def-weil-pbc-closed-subset-proper-over-base` identifies its composite with p as the properness condition. `def-pc-fibre-product` supplies the universal property giving the iterated-pullback identification. `lem-weil-pbc-closed-immersion-base-change` states exactly the closed-immersion conclusion required. The underlying subset is checked explicitly on affine charts: a prime contains IB precisely when its contraction contains I. This is an elementary ideal-containment check, not an assumption that reduction commutes with base change.

Step 2 uses `lem-weil-pbc-lft-base-change` to retain the local finite type hypothesis of the ambient morphism, `lem-weil-pbc-proper-base-change` for properness of the support scheme's pullback, and clause (1) of `lem-weil-pbc-closed-subset-proper-over-base-properties` in its some-closed-structure direction. I opened all three statements: their hypotheses match arbitrary v and locally finite type p, and none asks p to be quasi-compact. In particular 0CYL is applied to T prime over S prime, rather than to a non-finite-type morphism.

Step 3 views the given family as a cover of the identity object in S's small etale site and applies the statement of `lem-weil-pbc-fpqc-finer-than-etale`. Its statement explicitly gives the finite affine-image condition defining an fpqc cover; it does not assume individual members quasi-compact. The same local-finite-type leaf and 0CYL statement are used, now in the every-closed-structure direction, to turn the hypothesis on each closed subset C_i into properness of the actual pullback scheme Z_i. Step 1 already supplies that closed structure and its underlying subset.

Step 4 uses exactly the new 02L1 node: the morphism is Z to S, the covering is the fpqc family obtained in step 3, and its pulled-back morphisms are precisely Z_i to S_i. The properness conclusions of step 3 verify every premise. The support definition then gives the conclusion. This is not a direct citation of 0F4J standing in place of its argument.

For B and C, the new node introduces every object and cites the four actual definition nodes (schemes, fpqc coverings, fibre products, properness), has no proof or proof dependencies, and has its source's tag and label. DAG statements were searched for fpqc/proper descent and 02L1, and the entire blueprint was searched for 02L1 and fpqc locality. Only the field-extension special case below was found. Mathlib searches were run through msearch.py and retained in searches.jsonl; both semantic phrasings were read, along with Proper.lean and FlatDescent.lean. The returned target-locality and single-morphism universally-closed descent statements do not themselves state the arbitrary fpqc family result in one specialization. LeanSearch failed with Internal Server Error and is recorded as unavailable.

For E, I checked the local finite type premise at both applications of 0CYL, the exact pullback object used in 02L1, and the absence of any quasi-compactness hypothesis on the original morphism or cover members. Small cases include empty C, the identity cover, the empty covering over the empty base, and nonreduced pullbacks over inseparable field extensions. The general proper-descent node handles empty schemes and requires an actual covering, so an empty family cannot incorrectly prove properness over a nonempty base. The non-elementary inputs are all cited nodes; full statement quotations in citations.json ensure C4 mechanically, while the preceding checks explain which clauses are used.

## Not duplicates

lem-weil-pbc-proper-morphism-fpqc-descent vs lem-pc-proper-descends-field: the existing statement assumes a finite-type scheme over a field and pulls it back along a field extension; the new node is the ordinary proper-morphism theorem for arbitrary schemes and arbitrary fpqc covering families. The field node does not imply the new statement or the needed scheme-base case.

## Earlier second reading (a previous round; superseded)

- Item statement: checked against coherent.tex tag 0CYP and descent.tex tag 0F4J; the arbitrary base-change clause and etale-cover specialization have the stated locally-finite-type hypotheses and closed-subset conclusion.
- Step 1: checked against the statements of reduced induced structure, fibre products, and closed-immersion base change; the affine ideal-contraction argument identifies the inverse-image subset without assuming reducedness after base change.
- Step 2: checked against local-finite-type base change, proper base change, and the three equivalent closed-subset properness conditions; the hypotheses match and the constructed nonreduced pullback is permitted.
- Step 3: checked against etale-to-fpqc refinement, local-finite-type base change, and the every-closed-structure clause of 0CYL; the jointly surjective etale family supplies the required site covering.
- Step 4: checked against the new proper-morphism fpqc-descent statement and the definition of proper closed subset; the pullbacks are exactly those established proper in step 3.
- New node `lem-weil-pbc-proper-morphism-fpqc-descent`: checked against descent.tex tag 02L1; statement-only, self-contained, with all scheme, covering, fibre-product, and properness notions cited and recorded Mathlib searches.

That earlier second reading preceded the returned landing. The following repair supersedes its unchanged-delivery conclusion.

## Returned landing repair by NN

The return asked for a rebase onto the current DAG, rereading changed citations and adjusting the split. I ran the delivery dry run, which fetches origin/newtargets-dag and builds the overlay on that current baseline; its first preflight passed. I then reread every current statement cited in steps 1–4, including the current Mathlib leaves for closed-immersion, locally-finite-type, and proper base change. The reduced-structure statement still supplies the image C; 0CYL still supplies both the some-structure and every-structure implications with the locally-finite-type ambient hypothesis; the etale-to-fpqc statement still requires a small-site covering. No cited statement now invalidates the support argument.

I adjusted step 3 rather than leaving an unchanged re-push: it now cites def-weil-pbc-etale-site explicitly, whose statement makes arbitrary jointly surjective etale families coverings. Each S_i to S is an object, the target is the identity object, and joint surjectivity verifies the covering condition before the fpqc lemma is applied. All citation quotes were regenerated verbatim from the current node statements, with the new step-3 definition quotation included. The new 02L1 node remains a genuine generic morphism-descent lemma, not a restatement of either closed-subset clause. I reread coherent.tex 0CYL/0CYP and descent.tex 02L1/0F4J for this repair. Empty supports, identity covers and nonreduced pullbacks still satisfy every hypothesis. There is no statement change and no new search claim.


## Second reading by NN

- Item statement: checked both clauses hypothesis by hypothesis against coherent.tex 0CYP (`lemma-base-change-closed-proper-over-base`) and descent.tex 0F4J (`lemma-descending-property-proper-over-base`); correct with locally finite type ambient morphism, arbitrary base change, and arbitrary jointly surjective etale family. The etale case follows from topologies.tex 022C (`lemma-zariski-etale-smooth-syntomic-fppf-fpqc`), without quasi-compact individual cover members.
- Step 1: checked the actual reduced-structure clause (2), the support definition, fibre-product universal property, and closed-immersion base-change statement; correct after adding the existing open-fibre-product and affine-spectra statements to justify the affine computation. The two explicit tensor-quotient maps and prime ideal containment check supply the elementary algebra; reduction is never claimed to commute with base change. The assertion about properness is conditional, so it also applies when setting up clause (2).
- Step 2: checked locally-finite-type base change and proper base change against their current Mathlib-leaf statements, and 0CYL (`lemma-closed-proper-over-base`) clause (1) in the some-closed-structure direction; correct. The ambient morphism is locally finite type over the new base before 0CYL is applied.
- Step 3: checked the etale-site definition on its identity object, etale-to-fpqc statement against 022C, and 0CYL in the every-closed-structure direction; correct. Each actual pullback Z_i is a closed structure on C_i by step 1 and its ambient T_i to S_i is locally finite type by the cited base-change statement.
- Step 4: checked the new proper-descent statement at f = Z to S, with the covering from step 3 and exactly its pullbacks Z_i to S_i; correct. The original ambient p is locally finite type, so the support definition applies to the resulting proper Z to S.
- New node `lem-weil-pbc-proper-morphism-fpqc-descent`: checked against descent.tex 02L1 (`lemma-descending-property-proper`) and 02KO (`definition-property-morphisms-local`); correct descent direction for arbitrary fpqc families. Statement-only, all objects introduced, four definition citations checked, single-escaped TeX, accurate tag and label, no proof dependencies. Retained as a genuine generic tool, not a clause restatement: the item must still construct support schemes and use 0CYL. It is not a two-line consequence of existing nodes: existing separated descent is for a single surjective flat quasi-compact morphism, while the generic family-descent nodes require proving this descent property for properness. The existing field-descent nodes impose a field base and do not cover this statement.

Changes made and why:

- Added `lem-weil-pbc-open-fibre-product` and `lem-weil-pbc-fibre-product-affine-spectra` to step 1, with the explicit mutually inverse maps between (R/I) tensor_R B and B/IB. The previous ideal-containment sentence omitted the non-elementary identification of the affine pullback; the repaired argument cites its inputs and supplies the remaining short algebra.
- Made step 1's initial properness assertion explicitly conditional on C being proper, since step 1 also sets up descent, where that is the conclusion.
- Regenerated every citation quotation from the actual current node statement, including both added citations; each is verbatim.
- Tested removal of nested `split_report.tool_uses` against C8, then restored the first worker's original requests: review_split.py lines 99–100 explicitly implements a later human decision (2026-10-10 evening) permitting worker declarations inside split_report, with the reviewer judging them and the merge copying them into top-level tool_uses. The dry run requires these requests for the three off-unit generic facts. No top-level maintainer field is written. The generic facts are appropriate tools: reduced closed structures and 0CYL concern arbitrary ambient schemes, and 022C concerns arbitrary covers; none replaces the compact-support unit route. This newer tool contract and the older C8 wording should be reconciled by the maintainer.
- Ran independent Mathlib searches with vocabulary different from the first worker's: LeanFinder for separated/universally-closed proper descent, Loogle for DescendsAlong and IsProper, and grep restricted to AlgebraicGeometry for proper descent. Stored raw outputs and recorded them in the new node and searches.jsonl. Read Proper.lean (definition, target locality and base-change instances), FlatDescent.lean (universally-closed single-morphism descent), and the source Fpqc.lean family-descent signatures. None is an exact or one-line specialization of the new statement with all hypotheses discharged. Loogle's latest response reports overload, so it is recorded as unavailable rather than evidence of absence; the earlier successful Loogle search remains in place.

Duplicate checks: searched DAG tags and proper/fpqc keywords, opened the field-descent node, the generic family-descent nodes and the universally-closed, separated and locally-finite-type descent nodes. None already states generic proper-family descent. `blueprint_refs.py ancestor` confirms thm-cbc-finite-torsion; its whole-blueprint search and the independent search of imported blueprint text found no exact duplicate. The chapter, unit and ancestor compactification-refinement proof retain their route.

Small cases: C empty gives the empty closed support scheme and all its pullbacks; C = T over a field with the identity cover recovers ordinary properness; the empty family covers only the empty base (022B), where any scheme mapping to it is empty; a nonempty base cannot be covered by an empty family. For a purely inseparable finite field extension L/k, the pullback of Spec L along Spec L to Spec k may be nonreduced, but the two applications of 0CYL remain valid. No statement dispute or added hypothesis was found. No Lean was written and no compiler, Lake or build was run. The specified upstream-master directory is absent on this machine; no upstream sorry declaration was treated as proof evidence.
