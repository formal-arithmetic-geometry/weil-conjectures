# Stage-1 report: sk-lem-formal-closed-support

## Files written

- `dag/nodes/sec-six-functors-basics/sk-lem-formal-closed-support.json` — statement, split; no new nodes.
- `citations.json` — verbatim citations for both proof steps.

## Attachments

None. No new node was created.

## WANTED

None.

## What was wrong or changed

The imported proof was a sketch with direct finite-coefficient citations, an unused definition citation, and an `in_cycle` flag. Its all-coefficient argument is already stated by `det-lem-formal-closed-support-derived`, while the stratum calculation is already stated by `det-lem-formal-closed-support-stratum`. I replaced the four imported paragraphs with two composition steps using those existing nodes. The proof dependency list now contains exactly those two cited nodes. The target conclusions and coefficient-heart dependency are unchanged; the missing standing-scheme scope is corrected below.

## Review by NO

I read the target source `literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/sk-lem-formal-closed-support/_section.md` and its proof file, together with the existing statements of `det-lem-formal-closed-support-derived` and `det-lem-formal-closed-support-stratum`. The first cited node states the derived right adjunction, the derived-Hom form, and the fiber formula in the situation of the sheaf-level closed-support node. I checked that the target's standing-scheme convention supplies that situation, including the quasi-compact open complement, and that admissible coefficients match its coefficient hypothesis. The second cited node states the same closed/open factorization, finite locally projective module, dual, and natural four-term derived-Hom chain; its final isomorphism is exactly the target's part (2).

For step 1 I verified the multi-line quote against `det-lem-formal-closed-support-derived` verbatim and checked that it supplies every clause of part (1), including the `RHom` adjunction and the fiber identity. For step 2 I verified its displayed-chain quote against `det-lem-formal-closed-support-stratum` verbatim and checked the hypotheses and naturality in `K`. I removed the imported cross-unit adjunction and stratum-hom citations, the finite-coefficient support-triangle citation, and the unused sheaf-definition citation because the two detail statements in this unit already provide the required interfaces. I ran all required Mathlib search kinds for the item, including alternate LeanFinder/Loogle phrasings; the hits were only generic scheme or derived adjunctions, so the item is not a Mathlib leaf.

## STATEMENT-DISPUTED: missing standalone scheme scope

The imported statement used $X$, $Z$, and $S$ without introducing $X$ and did not state the standing-scheme hypothesis required by `det-lem-formal-closed-support-sheaves` and its derived consequence. Read literally for an arbitrary scheme, the proof cannot invoke those nodes: for example, on $X=\operatorname{Spec} k[x_1,x_2,\ldots]$ with $Z=V(x_1,x_2,\ldots)$, the complement is the non-quasi-compact union of the $D(x_i)$, so the standing Noetherian setting used by the cited closed-support construction is absent. I corrected the statement by introducing $X$ as a standing scheme and added `sk-def-sfb-dc-setting` to `stmt_deps`; this restores the source's intended setting without changing either conclusion or coefficient category.

## Second reading by NO

- Item statement: checked against `sk-lem-formal-closed-support/_section.md`, the standing-scheme definition `sk-def-sfb-dc-setting`, and the parallel detail-node statements; verdict: the missing binding/scope was corrected, with all clauses and admissible coefficients retained.
- Step 1: checked against the source proof paragraphs *Adjunction* and *Fiber formula* and the verbatim statement of `det-lem-formal-closed-support-derived`; verdict: its right adjunction, derived-Hom formula, triangle, and fiber formula cover every clause of part (1) under the corrected standing scheme.
- Step 2: checked against the source paragraph *The stratum formula* and the verbatim displayed chain in `det-lem-formal-closed-support-stratum`; verdict: the same $a=i\circ u$, finite locally projective $L$, and arbitrary $K$ give exactly part (2), including naturality.
- Existing-node audit: both cited nodes were opened in full; each says the fact used by its step. No new nodes exist, so B1--B7 and duplicate-node checks are vacuous; the recorded Mathlib searches were rerun with alternate LeanSearch, LeanFinder, Loogle, and grep phrasings and found no exact match.
- Edge cases: $L=0$, empty $S$ or $Z$, identity closed/open immersions, and $X=\operatorname{Spec} k$ reduce to the zero or ordinary adjunction formulas; no $n=0$ or $n=1$ parameter occurs.

Changes made: introduced the explicit standing-scheme scope, added its definition dependency, and recorded the type/scope correction above. The two composition steps, proof dependencies, citation quotes, and search log otherwise remain unchanged.
