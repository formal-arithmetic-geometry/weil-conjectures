# Stage-1 report: lem-sfb-koszul-immersion-smooth-ambient-independence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-koszul-immersion-smooth-ambient-independence.json: item split in five steps, using existing nodes only; not a Mathlib leaf.
- citations.json: one entry for every step/node pair, quoting the existing node's statement verbatim.
- searches.jsonl: command-generated Mathlib search record, retained without editing.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the live lean/WeilConjectures source for the exact blueprint tag and for Koszul/immersion/ambient-independence terminology. The Koszul immersion Ext and dualizing declarations found concern different statements. No declaration states the item exactly. Mathlib's AlgebraicGeometry.IsImmersion.of_comp is already recorded on lem-zl-immersion-cancellation; this delivery reuses that node.

## WANTED

None. The item source and all supporting sources are present locally.

## Corrections and route

The original statement agrees clause for clause with more-morphisms.tex Tag 069E (lemma-koszul-independence-factorization). It is retained. The old node had no proof. Its blueprint.from.node was null even though the recorded place and via chain identify det-thm-sf-ctf-stability-direct-images; filled that ancestor and retained the inherited place and via chain. Whole-blueprint searches for Koszul, 069E and immersion cancellation found no equivalent blueprint statement. Read the current latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof, rather than the historical snapshot in the unit metadata. The split preserves the inherited prerequisite chain; it makes no change to the unit or chapter.

The source suppresses two checks needed for its triangle lemmas: the product map is an immersion, and both product projections are smooth. Step 3 now cites the existing cancellation lemma, whose statement has no separatedness hypothesis. Step 2 proves the infinitesimal lifting condition directly and cites the existing arbitrary-base-change local-finite-presentation clause. This avoids creating a duplicate smooth-permanence lemma or imposing constant relative dimension. lem-sbc-smooth-relative-dimension-permanence has a fixed relative-dimension hypothesis, so it is not used for the unrestricted ambient schemes here. The existing stack-smooth-permanence lemma assumes a common field, so it is also not used.

## Review by NI

I read the complete statement and proof of Stacks more-morphisms.tex Tag 069E, and the statements and proofs of divisors.tex Tag 067S (lemma-lift-regular-immersion-to-smooth) and Tag 0693 (lemma-push-regular-immersion-thru-smooth). The latter explicitly treats Koszul regularity without Noetherian assumptions; its hypotheses require both maps from the source to be immersions. I also read morphisms.tex Tag 07RK(1), the smooth-base-change statement/proof Tag 01VB, and the DAG statements cited below. No SGA source is used. There are no new nodes whose sources need a separate review.

Step 1 uses def-weil-closed-immersion, which expressly defines an immersion as a closed immersion into an open subscheme. For an open U of the source, its complementary closed subset is closed in that ambient open under the closed immersion. Removing that subset realizes the restriction as a closed immersion into a smaller ambient open. Thus both restricted maps remain immersions, even when U is not the inverse image of an open under the whole original target. Koszul regularity of the first restricted map is precisely the neighbourhood assumption, not an uncited restriction theorem.

Step 2 uses def-pc-fibre-product for existence, pairing and uniqueness, def-sbc-smooth-morphisms for the affine first-order lifting definition plus local finite presentation, and clause (3) of lem-weil-pbc-qcqs-morphism-permanence for local finite presentation after arbitrary base change. I checked that clause (3) has no flatness or quasi-compactness hypothesis. The supplied thickening already maps to the new base, so the lifted map to the old smooth source pairs with that base map over S. Equality of both components checks the restriction. Exchanging factors gives the other projection. This is a short direct argument from those cited statements and definitions, marked elementary, rather than a missing node asserted by a tag. The other-unit lfp lemma is declared in split_report.tool_uses solely as this generic geometric tool.

Step 3 uses the same fibre-product statement for pj=i and qj=i-prime, and lem-zl-immersion-cancellation for the assertion that an immersion composite implies its first factor is an immersion. The full statement was read: it applies to arbitrary scheme morphisms and has no separatedness assumption. Its Mathlib source, Immersion.lean:218, confirms the cancellation direction. This supplies the actual hypothesis of the next two steps, rather than silently treating the product map as a closed immersion.

Step 4 uses the statement of lem-sfb-koszul-immersion-smooth-lift exactly with Z=U, its P=Q and its S=P. The cited node says the smooth ambient triangle carries Koszul regularity of the composite to the upper immersion. Smoothness is from step 2; the two immersions are from steps 1 and 3; the equation is from step 3; regularity of the composite is from step 1. Step 5 uses lem-sfb-koszul-immersion-smooth-push with the other projection and base P-prime. Its statement supplies the reverse direction in a smooth triangle. The same checks hold, and regularity of the upper map is now step 4. Interchanging the two ambient schemes repeats precisely these applications and gives the converse implication without a new hypothesis.

I checked the statement and these applications on identity immersions, empty source, empty Koszul sequence, and varying local codimension. For example the identity of any scheme and its zero section in the affine line compare an empty sequence with the regular sequence (x), including over a non-Noetherian ring. Nonseparated smooth ambient schemes cause no problem because cancellation gives an immersion, which is all the two triangle lemmas assume. There is no claim that the graph is globally closed or that a smooth morphism has a single global relative dimension. No flatness of T over S, finiteness, separation or Noetherianity is introduced. All proof steps are shorter than 2000 characters and contain no hidden comparison sublemma.

I checked delivery-errors B--E: no new statement-only node, duplicate, clause-restatement, hidden non-elementary tag citation, cycle through the item, or unjustified source hypothesis is introduced. All seven distinct cited statements were read and the quotes in citations.json are their actual full statements. The item searches were executed through msearch.py (LeanFinder with two distinct phrasings, LeanSearch, Loogle, grep), and their actual hits read. The grep hits concern Koszul connections, a local-cohomology comment, and RegularSequence.lean:21's TODO, which was opened; none states the item. Earlier inherited searches remain in the item as provenance; the five searches run for this delivery are appended from searches.jsonl. No Lean source was written or compiler invoked.

## Not duplicates

No new nodes. Existing smooth-lift, smooth-push, fibre-product, lfp-base-change and immersion-cancellation nodes are reused directly.

## Unfinished work

None in the one-level split. The cited lift and push nodes remain separate queue items as required.

## Validation

The required server-side deliver.py --no-push invocation exited 0 and printed OK (not pushed), with preflight passed at 8f40d481f43. This includes the server DAG and split checks. A final dry run follows the correction of a report-only citation count (seven distinct cited nodes).
