# Stage-1 delivery: lem-sfb-adjunction-abstract-iso-unit-counit

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-adjunction-abstract-iso-unit-counit.json — statement; Mathlib leaf, exact theorem for each of its two clauses. No new nodes.
- citations.json — empty list: this Mathlib leaf has no proof steps or proof citations.
- report.md — this report.

## Attachments

None. The project-source search by blueprint tag and by unit/counit-isomorphism terminology found no project declaration stating the general item. In WeilConjectures/Mathlib/CategoryTheory/Monad/Adjunction.lean, CategoryTheory.Adjunction.isIso_unit_of_iso_id (line 25) and isIso_counit_of_iso_id (line 30) assume endofunctors and an isomorphism L ≅ id, rather than the item's arbitrary pair of categories and isomorphism of a composite. These special cases are not attachments. The matching general declarations belong to Mathlib.

## WANTED

None. The exact statements and their proofs are present in the pinned Mathlib. No additional literature is needed to establish this leaf; I did not rely on the historical Johnstone attribution in the inherited source field.

## Findings and changes

The inherited candidate is correct. Clause (1) is CategoryTheory.Adjunction.isIso_unit_of_iso, Mathlib/CategoryTheory/Monad/Adjunction.lean:113-114; clause (2) is CategoryTheory.Adjunction.isIso_counit_of_iso in the same file:142-143. I read the surrounding variables, constructors and proof bodies at lines 37-143. The declaration of the natural isomorphism in each hypothesis is unrestricted; it need not have the unit or counit as a component. Lean's L ⋙ R denotes R after L, and R ⋙ L denotes L after R, so the apparent reversal of composition notation is not a statement discrepancy.

Changed status from unsplit to mathlib, filled mathlib_match with both full declaration names and source lines, and supplied split_report and document proof_origin for the existing Mathlib proofs. The first dry run requested a non-null proof_origin even for this Mathlib leaf; I supplied that provenance without adding proof steps. Kept the statement, its two statement dependencies, source, ancestor reference, and historical candidate. Replaced the two inherited reviewer grep summaries by four queries actually executed through msearch.py in this sandbox, recorded verbatim from searches.jsonl with their observed hits. All four services answered successfully. LeanFinder and LeanSearch returned both exact theorems, Loogle returned the exact unit theorem, and grep returned the two exact signatures and line numbers. A second absence search was unnecessary because the exact matches were found.

The whole-DAG declaration searches found this item and applications of the same Mathlib theorems to special settings, rather than a need to create a generic duplicate. Whole-blueprint searches for adjunction, abstractly and unitAsIsoOfIso found no blueprint node stating both general assertions; the last two searches had zero hits. The ancestor command confirms sk-lem-formal-closed-support. Read the chapter and unit records and the current literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-formal-closed-support/_section.md. This is the generic tool used to justify the actual closed counit and the open adjunction unit/counit in that route, rather than a replacement for any geometric step. The existing blueprint.from.place is already specific and same_as remains [].

## Unfinished work

None for stage 1. No Lean file was written and no compiler, Lake or build was run. The item is delivered as a Mathlib leaf rather than split into redundant clause nodes.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to distinguish.

## Review by NF

I checked B--E of coord/delivery-errors.md against the actual node and the pinned source. For B, the existing statement introduces both categories, both functors, the adjunction, and its unit and counit; def-nagata-category defines the category notion and lem-weil-pbc-adjunction-of-natural-bijection supplies the adjunction, its unit/counit and triangle identities. I opened both statements rather than inferring their content from their titles. The Mathlib match names a separate exact declaration and correct lines for each clause; there are no auxiliary unsplit nodes, undefined data or added hypotheses.

For C, there are no numbered proof steps to audit: status mathlib intentionally leaves proof and proof_deps empty. Thus citations.json is [] and no non-elementary fact is silently attributed to a definition or to a node with a weaker statement. This is justified by the exact two-clause leaf rule B8, not by marking the whole theorem elementary. For D, neither clause was relabelled as a new node and nothing was pushed into a disguised copy of the item; both proofs already live in Mathlib.

For E, I checked the universes and hypotheses at lines 37-41: C and D are arbitrary categories, L:C→D and R:D→C, without a smallness, linearity, abelian, full-faithfulness or equivalence assumption. The two declarations require precisely the adjunction and the relevant natural isomorphism. The implementation of unitAsIsoOfIso at lines 100-110 has hom := adj.unit, and counitAsIsoOfIso at lines 128-140 has hom := adj.counit; hence the conclusion is about the actual adjunction maps, not an arbitrarily chosen comparison. Their displayed proofs contain no sorry. I checked empty and terminal identity categories, where the assertions are vacuous or identities, and the identity functor adjunction twisted by an arbitrary natural automorphism a (unit a, counit a inverse), where the hypotheses hold even when the supplied composite isomorphism is the identity and differs from a. The conclusions correctly give invertibility without claiming equality to that supplied isomorphism. No correction to the statement or the unit route was needed. There are no long proof steps hiding a lemma and no SGA source was used.
