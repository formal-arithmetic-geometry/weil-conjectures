# Worker report

Group Q158; item lem-dl-a1-etale-base-change-inertia-square; stage 1, 2026-10-22.

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-dl-a1-etale-base-change-inertia-square.json: statement item, split into six steps; no whole-item Mathlib match.
- citations.json: nine step/node pairs, quoting the cited statements verbatim.
- report.md: this report. searches.jsonl contains the five actual Q158 searches. write_split.py is a sandbox-only writing helper, not delivery content.

New nodes: 0. New Mathlib leaves: 0. The statement is unchanged. Its statement dependencies now include the existing definition def-weil-ring-localization-away because the last clause uses principal localizations.

## Attachments

No attachment of the complete item was found. Searches of lean/WeilConjectures by its blueprint tag, inertia, base change and fixed/invariant-ring terminology found specialized integral-closure and Dedekind-domain results, not its arbitrary-ring statement. The existing node lem-dl-a1-flat-base-change-finite-invariants is already attached to AlgHom.tensorFixedPointsEquiv and AlgHom.coe_tensorFixedPointsEquiv_tmul; I read these declarations in WeilConjectures/Mathlib/RingTheory/TotallySplit.lean:78 and :86 and reused the node, without requesting a second attachment.

## WANTED

None. All mathematical sources needed are present in literature/stacks-project/.

## Audit and corrections

The imported item had no proof. Its statement accurately records the reduction in Stacks 0BST together with 0BSS, and no statement dispute was found. I retained its statement, source, blueprint ancestry and pre-existing search history. The group Q158 searches were appended, with their actual query strings and results, rather than replacing the earlier group's work. The original attempt began from the imported node. On this continuation a completed sandbox split, report, citations and five logged searches were already present; I retained them, compared the item with the current unsplit live node, and reopened all eight cited statements and the Stacks sources. The statement and blueprint ancestry still agree with the live node, and there is no released repair note.

The proof of inertia equality is written out, rather than moved into a new node restating one clause. The flat-invariants comparison was found by searching the whole DAG for 0BRH and lemma-base-change-invariants, and is reused exactly in its A-algebra formulation. Two applications are legitimate with the same base A: both G and its subgroup I act by A-algebra automorphisms, so no separate assertion about flatness over R^I is required. The affine fibre-product and etale-base-change results, etale flatness and principal etale localization all already have Mathlib-leaf nodes. No supporting node was necessary.

Whole-blueprint searches (inertia; inertia invariant; finite group; flat invariants; base change etale) and DAG tag/keyword searches found no blueprint node stating this square. rem-dl-a1-conventions and the boundary-stalk nodes concern lisse sheaves and not this ring lemma. The parent lem-dl-a1-finite-group-inertia-invariants-etale is the larger local-etaleness theorem; citing it here would be circular, so it is not used. I read the chapter and unit records and the main-20261015 conventions text. The unit has no proof steps, and this item is not its key node; no realized fields are changed.

## Unfinished work

None at stage 1. No Lean was written, no compilation was run, and no source checkout or launcher file was changed. All writes are in the assigned sandbox. Server validation and push are recorded below once completed.

## Not duplicates

No new nodes were created. Existing generic lemmas were used instead of making copies of 0BRH, 02GO, 01JQ, or 00U2.

## Review by Q158

I read pione.tex Tags 0BSS (lemma-inertia-base-change) and 0BST (lemma-inertia-invariants-etale), including the two initial reduction paragraphs and the displayed square. The item asks for exactly the inertia equality, both canonical invariant isomorphisms, the cartesian square with etale horizontal arrows, the indicated point and its principal localization version. The ring is arbitrary: the text neither assumes R finite over A nor divides by the group order. I checked the extension to localizations against algebra.tex Tag 00U2 (lemma-etale), clauses (1), (2) and (6), and the affine/scheme conventions against morphisms.tex 02GJ and 02GO. There are no new statement-only nodes whose source needs a separate review.

Step 1 uses only def-weil-pbc-module-tensor-product, whose statement says that pure tensors generate the module. On each such generator the difference is in the extended ideal of q. Conversely contraction tests the difference of every r. The inertia/difference criterion is proved in the step: finite order makes the stable-ideal inclusion an equality, then the quotient identity fixes every fraction. This is the short generator calculation underlying 0BSS, not an uncited theorem about fibres or a hidden residue-field comparison. In particular it needs no flatness, faithful action, or domain assumption on R itself.

Step 2 uses the statements of lem-weil-pbc-etale-algebra-flat and lem-dl-a1-flat-base-change-finite-invariants. I opened both nodes: the former gives flatness from precisely the assumed affine etaleness, and the latter gives the B-algebra isomorphism with its canonical pure-tensor map for any A-algebra action of a finite group. A=R^G is fixed by every element of I as well as G. Thus its hypotheses are satisfied for both applications. I also read more-algebra.tex 0BRH (lemma-base-change-invariants): its flat-case proof is the exact-sequence argument, without a Reynolds operator. The cited node's more general A-algebra formulation is already Lean-closed. The explicit unit-tensor isomorphism reduces the G case to B, preserving the specified canonical map.

Step 3 uses lem-weil-pbc-fibre-product-affine-spectra, whose statement specifies the tensor product and both projection maps, not merely affineness or the existence of a pullback. I checked schemes.tex 01JQ (lemma-fibre-product-affines) and 01I4 (lemma-fibre-product-affine-schemes). The pure-tensor formula in step 2 makes the square the requested canonical square. Step 4 uses lem-weil-pbc-etale-scheme-base-change, read in its node and morphisms.tex 02GO (lemma-base-change-etale): the base change is arbitrary, so Spec R^I needs no finiteness or field hypothesis. The other horizontal morphism is etale by hypothesis. No claim that the vertical maps are etale is smuggled into this item.

Step 5 uses def-weil-affine-spectrum for the contravariant ring-induced morphism. The contraction equality is checked element by element using Q intersect R=q; it requires no surjectivity of any map of spectra. Step 6 cites lem-weil-pbc-etale-algebra-finite-presentation-localization only for its clause (2), which gives A to B_b etale for every b. I read that node and its 00U2/02GJ sources. The finite-presentation conclusion of clause (1) is not used. I also opened def-weil-ring-localization-away: it gives the fraction equality relation and ring operations used in the written tensor/localization maps. The tensor definition supplies pure-tensor generation and relations. The inverse formulas show the actual equivariant identification. The condition b not in Q intersect B makes the quotient localization a nonzero domain; primality proves contraction. Thus every hypothesis of steps 1--5 is verified before applying them again. This establishes all localized conclusions, not only the localized inertia group.

For B1--B9 there are no new node files to test; the item has complete steps, source tags, explicit objects, filled ancestry and searched same_as. For C1--C5 I opened every cited node and used its statement only; nine verbatim citations are in citations.json. The other steps' conclusions are used sequentially, and proof_deps is exactly the union of uses. For C6 no new or parent-dependent lemma is cited. For C7--C8 there is no undeclared tool: each off-unit theorem cited is an existing Mathlib leaf, and the sole project comparison is closed and belongs to this unit. For D1--D5 no clause has been relabelled as a new lemma and no omitted source argument is left as an assertion. No step exceeds 2000 characters.

For E1--E7 I tested G trivial, I trivial, I=G, B=A, R a field, rings with nilpotents and a trivial finite group action in characteristic dividing |G|. The formulas still give the claimed maps and identities. For B=0 there is no prime Q, so there is no overlooked nontriviality assumption. Non-faithful actions also satisfy the difference criterion. In the localized case b=1 recovers the original statement; b nilpotent cannot meet the stipulated complement of Q. Non-faithfully-flat etale B is allowed because no descent or injectivity of B into S is used. The finite-order ideal argument and fraction calculation address the potentially missing hypotheses explicitly. No repair to the statement or route was necessary.


## Repair of landing refusal, 2026-10-23

The return has one point: the approved side-project completion was not promoted to the live DAG read by the queue. I treated that as an instruction to rebase and resubmit, not as a mathematical rejection and not as permission to mark the item reviewed myself. The retained receipt names the earlier prepared head 0d4f02b2c22. I first ran the required dry run before editing the existing split; it completed successfully at 13d3b2c5de1. The delivery tool fetched the current server origin/sheaf-dag and rebuilt the delivery on that base, preserving the current maintainer-owned fields.

I compared the retained node with the current read clone: statement, source, blueprint ancestry, creation stamp, chapter and unit agree exactly. The current item is unsplit with an empty proof. The retained differences are precisely the six proof steps, their dependency union and origin, the additional localization definition dependency, five appended logged searches, split status and the split report. I retained these contributions and refreshed the split report to identify this repair. No repair-note file is present in the current read clone. No definition or target statement was changed.

I reopened all eight cited nodes rather than assuming the earlier approval remained sufficient. Every one of the nine quotations in citations.json is still a verbatim substring of the current statement, so none needs replacement. Step 1 uses the tensor definition's generation by pure tensors and the written finite-order/difference calculation. Step 2 uses etale-algebra flatness and the existing finite-invariants node with base A, algebra R, and finite group G or I; the latter still states the general A-algebra version and still has its closed upstream attachment. Step 3 uses the affine fibre-product formula with its two specified maps. Step 4 uses stability of etaleness under arbitrary base change. Step 5 uses the ring-induced spectrum morphism and the displayed contraction calculation. Step 6 uses only clause (2) of the localization theorem, not clause (1), together with the tensor and localization definitions for the explicit inverse formulas and the prime calculation. Thus the present cited statements justify exactly the same applications; no change of proof route or replacement dependency is needed.

I reread pione.tex, lemma-inertia-base-change (0BSS) and the first two reduction paragraphs of lemma-inertia-invariants-etale (0BST), as well as more-algebra.tex, lemma-base-change-invariants (0BRH). The item remains the cartesian-square reduction and not the stronger local-etaleness conclusion of its parent. In particular inertia equality is independent of flatness, whereas the invariant comparisons use flatness of B over A; both uses have the correct hypotheses. Localization uses b outside the contracted prime, and does not need B to be faithfully flat. I checked the trivial-group, identity-base-change and b=1 cases again; the zero algebra has no prime to instantiate the statement. All six steps are under 2000 characters. No supporting lemma is hidden by this rebase, no new node or Mathlib leaf is introduced, and no additional search was necessary because neither the statement nor the search question changed. The prior sources, report, citations and complete search log are retained.

This section supplements my signed Review by Q158 above and discharges the sole return point by a freshly based, reviewed delivery. Final server validation and push follow this report update through the prescribed delivery command.
