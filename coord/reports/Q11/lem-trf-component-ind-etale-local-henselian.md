# Q11 stage-1 delivery: lem-trf-component-ind-etale-local-henselian

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-component-ind-etale-local-henselian.json`: statement; split into seven proof steps; no exact Mathlib match.
- `citations.json`: eight step/node citations, each quoting the statement actually used.
- `searches.jsonl`: five real searches performed through the required msearch command. The item's four inherited Q48 search records are preserved and distinguished from these fresh Q11 searches.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. The statement, statement dependencies, source, creation record, chapter, unit and blueprint ancestry are unchanged. Only the sandbox was written; no git command was run in the shared repository, no Lean was written and no compiler or build tool was run.

## Attachments

None. Searches of `WeilConjectures/` in the read-only slopmaster2 source for the exact blueprint tag and id, `componentRing`, `componentIdeal`, component/ind-etale combinations and the ind-etale files found no project declaration proving the whole item. General ind-etale and quotient-localization facts do not constitute an attachment for the component statement.

## WANTED

None needed for this split. The inherited Hübner–Schmidt reference explains the parent application's component convention. This proof uses the available local Stacks sources, not an unread PDF or an SGA reference.

## What was wrong and what changed

The imported node was statement-only. Its assertion is correct; no STATEMENT-DISPUTED or statement correction is needed. Tag 00EG provides the component ideal convention, but does not by itself assert ind-etaleness. The proof now supplies the missing finite-idempotent diagram and quotient-colimit argument. The final henselian clause is only the universal hypothesis applied to the chosen component; it is not a theorem transferring henselianity through arbitrary quotients.

I did not introduce a separate node for the finite-family idempotent formula or quotient colimit: both are explicit elementary calculations. Conversely the localization comparison, open-immersion/etale implication, finite presentation and ind-etale composition are cited as the non-elementary facts they are. Thus the argument remains in the item instead of being renamed as a new lemma. A source-tag typo found during self-review was corrected from 097H to 097I, the tag whose label actually is `definition-ind-etale`.

## What could not be finished

Nothing mathematical remains in this one-level split. Formal Lean implementation is outside the authorized stage.

## Not duplicates

No new nodes. Existing `lem-weil-pbc-fg-idempotent-ideal-idempotent-generator` already supplies the quotient/principal-localization comparison; existing `lem-weil-pbc-principal-localization-open-immersion`, `lem-weil-pbc-etale-composition-cancellation`, `lem-weil-pbc-etale-algebra-finite-presentation-localization` and `lem-weil-pbc-ind-etale-stability` supply the other tools. The affine etale cover component criterion was read but is unnecessary here: its additional equivalence would add an irrelevant hypothesis or dependency.

I searched all `dag/nodes/` for 00EG, 097K, idempotents, component quotients, localization and quotient colimits, and ran `tools/blueprint_refs.py search` for `idempotent`, `idempotents`, `idempotent ideal`, `component`, `component ring`, `component quotient`, `ind-etale` and `filtered colimit of etale`. No imported blueprint node states this item in another form; `blueprint.same_as` remains empty. The ancestor tool confirms `lem-trf-local-term-locality`. Its Artin joins reduction through the parent tensor theorem is the same route as before. No chapter or unit file was changed.

## Mathlib search assessment

The five Q11 searches are recorded with their exact queries in the node and in `searches.jsonl`: two LeanFinder phrasings, LeanSearch, Loogle and grep. Every service returned successfully. The useful hit `IsLocalization.Away.quotient_of_isIdempotentElem` is already carried by the existing idempotent-generator Mathlib leaf. Formally-etale quotient criteria alone do not imply the filtered-etale presentation. Abstract commutative-ring colimit constructions alone do not identify this diagram or its etale stages. Standard-etale presentations, local criteria and loci are also not the full item. Thus neither an attachment nor a one-line Mathlib specialization proves every clause.

## Review by Q11

I read the item, its parent tensor theorem, the chapter and unit records, the three blueprint levels in SETUP, the stage-1 rules and delivery-errors B–E. For the item I read Stacks `algebra.tex`, Tags 00EG (`lemma-connected-component`) and 00EH (`lemma-ideal-is-squared-union-connected`), including the proof that the quotient by an idempotent ideal is the complementary principal localization. I also read 00U2 (`lemma-etale`), and `proetale.tex`'s ind-etale definition and composition lemma (097I and 097K). The assembled presentation proof is correctly marked as written by an agent; it is not falsely attributed verbatim to 00EG. There are no new nodes whose sources or statements need review.

Step 1 is elementary: the index is finite subsets of a set of ring elements, hence small, nonempty and directed by union. The formula d_F = 1 - product(1-e) is idempotent; adjoining one generator gives d_(F union {e}) = d_F + e - d_F e, and e d_F = e for e in F proves the reverse ideal inclusion. Thus every comparison in the diagram is an actual canonical quotient map, whose compositions agree on representatives.

For step 2 I opened `lem-weil-pbc-fg-idempotent-ideal-idempotent-generator` and checked part (2), not just its title. It requires an idempotent u_F, a surjection and kernel (1-u_F)T. Our quotient has precisely that kernel because J_F = (d_F). Its conclusion is an isomorphism induced by the given map and so respects the T-algebra structures. The citation quote includes this clause. No finite generation assumption on the whole component ideal is imposed.

For step 3 I opened all three cited nodes. `lem-weil-pbc-principal-localization-open-immersion` says the principal localization has open-immersion spectrum map; `lem-weil-pbc-etale-composition-cancellation` explicitly says open immersions are etale in clause (1); `lem-weil-pbc-etale-algebra-finite-presentation-localization` explicitly turns an etale affine spectrum map into a finite-presentation algebra in clause (1). I do not infer the latter two facts from a definition node. The only isomorphism used is the structural T-algebra isomorphism already supplied by step 2. Local Stacks 00U2(1), 01I3 and 02GP support this chain.

Step 4 cites only the colimit definition, which I read: it is used as a universal property and not as a colimit-existence theorem. The proof verifies that property. A cocone's empty-stage leg defines g:T→C; singleton compatibility kills every generating idempotent; the ideal quotient gives the map T/I_Z→C. Evaluation on arbitrary t shows it factors every leg, and quotient surjectivity gives uniqueness. This is one routine quotient universal-property argument, not an unproved continuity lemma. It works in T-algebras, the category used by the ind-etale definition, and its index is the small filtered poset established in step 1.

Step 5 applies precisely the definition in `def-weil-pbc-ind-etale-algebra`, whose statement explicitly requires etale finite-presentation stages. Those requirements were both checked in step 3. Step 6 uses the actual composition clause of `lem-weil-pbc-ind-etale-stability`; I read its statement, confirmed both maps are ind-etale, and retained the given structural composite A→T→T_Z. This generic node is on the inherited proper-base-change route; no replacement of a unit's argument is being made.

Step 7 is universal instantiation of the hypothesis for our particular Z. The cited henselian terminology node defines the phrase used; no theorem is extracted from that definition. I checked the zero ring (no components), a connected ring (E consists only of 0, so the system gives T itself), a two-factor product (the complementary factor is removed by a single idempotent), and an infinite product of F_2's. In the last example nonprincipal-ultrafilter components need not be open, but the finite-idempotent diagram still gives their quotient ring; the proof never asserts the entire component ideal is principal. Nilpotents cause no problem because the construction uses the stated idempotent-generated ideal, not the radical ideal of the underlying closed subset.

Against B: all existing metadata and the exact statement remain, every notion in the statement retains its definition dependency, TeX is stored once, actual Stacks labels were checked, and search outcomes are honestly recorded. Against C: every cited statement was read and quoted, every non-elementary input has a node, no proof of another node is used, and the dependencies go to existing generic tools, never to the parent or a descendant. Against D: the item's own diagram and universal-property proof carry its substance; there is no new restatement node. Against E: all localization, quotient, finiteness and composition hypotheses have been checked at their application. No proof step exceeds 2000 characters. During self-review I fixed the definition tag and removed an accidental prose backslash before an apostrophe. No mathematical statement was changed.

## Validation

The required `deliver.py Q11 lem-trf-component-ind-etale-local-henselian --no-push` exited 0 and printed `OK (not pushed) ... at 450d776286: preflight passed`. Server preflight, including the DAG and split checks, passed. The dry-run process has exited before the push invocation. No mathematical changes followed the passing check.
