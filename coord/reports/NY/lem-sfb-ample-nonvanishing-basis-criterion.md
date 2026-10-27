# Stage-1 delivery: lem-sfb-ample-nonvanishing-basis-criterion

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-ample-nonvanishing-basis-criterion.json: existing statement, now split into four steps. Mathlib verdict: no exact match or one-line specialization. No new nodes; zero Mathlib leaves.
- citations.json: six entries, one per cited node per step; each quote was compared literally against the current repository statement.
- report.md: this report. searches.jsonl is the unmodified search-command log.

## Attachments

None. Searched all lean/WeilConjectures for the exact item tag and the notions ample/basis and nonvanishing/basis. There is no declaration stating this equivalence. Ample.lean defines IsAmple and nonvanishingLocus; the positive-power, finite-cover, pullback, and canonical-Proj results cover only auxiliary facts. A partial statement is not treated as an attachment.

## WANTED

None. All sources used are in literature/stacks-project.

## Findings and changes

The statement is unchanged. It is exactly the equivalence of (1) and (3) in Stacks Properties Tag 01Q3, label proposition-characterize-ample. In particular, condition (3) does not assume that its opens are affine. The previously empty proof needed that affineness argument; I wrote it using the existing lemma for intersections with affine opens, not a new node repeating one implication of the item.

The forward implication uses existing canonical affine Proj charts and a standard-open basis. I did not use lem-sc-ample-proj-open to claim a section-compatible open immersion: its statement supplies an unspecified graded ring and open immersion, without the inverse-image identity required here. Instead lem-sc-ample-proj-local-chart supplies the same map for all sections, the exact inverse-image formula, and the needed local isomorphism. This is the C4 distinction on which the forward proof depends.

Read the chapter and unit records and the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and proof. The unit record is historical and differs from the latest blueprint, but neither has an ampleness step at this level; this item is an inherited lower-level generic tool. Its existing blueprint.from.node is null, as confirmed by blueprint_refs.py ancestor; I preserved it and its ancestry, and explained the inherited place in split_report.blueprint. Whole-blueprint searches for ample, nonvanishing, and basis for the topology found no matching blueprint statement. The three cross-unit generic proof tools are declared in split_report.tool_uses. No chapter, unit, upstream source, or other node was edited.

## Not duplicates

No new nodes. Reused lem-sc-ample-proj-local-chart, lem-sc-proj-standard-open-basis, lem-weil-pbc-affine-opens-basis, and lem-sc-affine-cap-section-open, after opening their statements. Searches by Tags 01Q3, 01Q1, 01PX, 01PV, 01PW, 01PS and relevant keywords located these existing tools. lem-pc-ample-affine-loci-criterion is restricted to proper schemes over a field and identifies projective ampleness; it is not the arbitrary quasi-compact-scheme equivalence here. lem-sc-ample-proj-open lacks the section correspondence. None was duplicated.

## Review by NY

I read Properties 01Q3 (proposition-characterize-ample), including its explicit (1) to (2) to (4) to (3) route and its reference to 01PX for (3) to (1). For the chart argument I read 01Q1 (lemma-ample-immersion-into-proj) and checked the statement of 01PZ through the existing chart node. I also read Algebra 00JP (lemma-topology-proj), especially (5), and Constructions 01MB (lemma-proj-scheme); these justify the existing positive-degree affine standard-open basis. For the reverse implication I read Properties 01PX (lemma-affine-s-opens), 01PV (lemma-affine-cap-s-open), Definition 01PS (definition-ample), and Schemes 01IT (lemma-basis-affine-opens). There are no new nodes requiring additional source reviews.

Step 1 uses the ampleness definition's affine section neighborhood and its cover clause, then the precise statement of lem-sc-ample-proj-local-chart. Its cover hypothesis holds because ampleness supplies such a section at every point. Its isomorphism clause requires both ampleness and affineness of X_a, which we have. The section ring in this step is exactly the ring in that node. No finiteness, separatedness, or quasi-separatedness is added as a hypothesis of this application.

Step 2 uses the statement of lem-sc-proj-standard-open-basis, which explicitly restricts to positive-degree homogeneous elements. The local chart isomorphism sends V intersect X_a to an open W inside D_+(a); since that chart is open in Proj, W is open in Proj. The basis gives D_+(t) contained in W. The already obtained inverse-image formula first puts every point of X_t into X_a and then into V by the chart isomorphism. This spells out the containment, without assuming that arbitrary inverse images under a continuous map form a basis, or silently using a global embedding. The positive degree n is retained, and the homogeneous element is exactly a global section of L to that tensor power.

Step 3 uses lem-weil-pbc-affine-opens-basis only for an affine neighborhood of a point, a clause explicitly stated there. It then applies the item's assumed basis condition, not any as-yet unproved ampleness claim. The statement of lem-sc-affine-cap-section-open explicitly includes sections of positive tensor powers; it imposes neither separatedness nor Noetherianity. Its affine intersection U intersect X_s equals X_s because the latter is contained in U. Arbitrary open subsets of affine schemes are never asserted affine.

Step 4 uses only the two conditions in def-weil-pbc-ample-invertible-module: the given quasi-compactness and the affine section neighborhoods of Step 3. It is elementary assembly. Every non-elementary assertion in all four steps is the statement of an explicitly cited existing node, and citations.json quotes those statements verbatim. No source proof was used as if it were an uncited statement.

Small cases checked: the empty scheme makes both pointwise conditions vacuous and satisfies quasi-compactness; a one-point affine scheme with the trivial line has the unit section; on any affine scheme the trivial line gives usual principal-open refinements; a zero section only yields the empty locus and cannot be chosen through a point. Positive-degree homogeneous elements are required even if the section ring has missing degrees. The proof never intersects two arbitrary affine opens and never requires a non-affine scheme to be separated beforehand. A non-separated scheme cannot acquire an ample line by this argument unless it actually satisfies the strong basis hypothesis; 01PV remains valid without separatedness. Quasi-compactness is used in the final definition, not manufactured by a finite-cover argument. No Noetherian or finite-type assumption has entered.

Against delivery-errors B--E: no new node can be elementary, duplicate, or a restated clause; the statement remains self-contained and uses its existing notion definitions; TeX is single-escaped and sources use tags with labels. The four steps are 508, 590, 482, and 294 characters, so none hides a long inline lemma. There is no circular use of this criterion and no new child hiding the proof. The only elementary step is the last definition check. I recorded only searches actually run by msearch.py, preserving their exact tool and query text, and read the returned types. The second phrasing returned Proj.isBasis_basicOpen and affine basis declarations, which are partial tools, not this equivalence. Inspected Mathlib ProjectiveSpectrum/Basic.lean:79: its all-elements basis does not itself say anything about an arbitrary invertible module being ample. The grep found no IsAmple or ample/basis theorem in Mathlib's AlgebraicGeometry. No unavailable service was reported as an absence result.

## Unfinished work

None in this one-level split. The existing dependencies retain their own independent proof states. No Lean file was written and no compiler or Lake tool was invoked. Server dry-run and push results follow below when available.
