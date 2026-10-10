# Stage 1 report: pqf-def-locnoeth

## Files written

- `dag/nodes/sec-nagata-compactification/pqf-def-locnoeth.json`: definition, split; no new nodes; Mathlib candidate recorded.

## Attachments

None. No declaration in the project source states this blueprint definition exactly, and the available `IsLocallyNoetherian` declarations are Mathlib declarations rather than project declarations.

## WANTED

None.

## What was checked and changed

The item was copied from the repository and checked against the blueprint source `literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-zmt/pqf-def-locnoeth.md` and the cited Stacks source, Morphisms, Tags 01T6 and 01T5. The statement was kept unchanged. Its only mathematical object dependency is the scheme notion, recorded as `def-pc-scheme`.

The full DAG and blueprint were searched for the definition and for the two cited tags. No existing node states the same definition or the open-subscheme consequence. The slopmaster2 and source project trees were searched for the blueprint tag and for locally Noetherian declarations; no sorry-free project declaration attaches to this item.

Mathlib source `Mathlib/AlgebraicGeometry/Noetherian.lean` was read at the class definition (lines 57-59), the affine-cover construction (lines 103-105), the affine-open-cover equivalence (lines 131-135), and open-immersion preservation (lines 151-159). These declarations cover the core definition, the affine-cover formulation, and the open-subscheme clause. Because identifying the Stacks existence-of-cover definition with Mathlib's all-affine-open class uses the theorem `isLocallyNoetherian_iff_of_affine_openCover`, the item is recorded as a split definition with `mathlib_candidate`, not as a Mathlib leaf. The required LeanSearch call was unavailable; its result is recorded as unavailable, while LeanFinder, Loogle, and grep returned the declarations above.

## Review by H1

I checked the item's source and every clause of its statement. The affine-cover definition is the Stacks Tag 01T6 notion; the open-subscheme assertion is the Tag 01T5 consequence for an open immersion, and the final morphism-situation sentence is terminology defining the target condition. I verified that Mathlib's `IsLocallyNoetherian` class supplies the Noetherian condition on affine opens, that `isLocallyNoetherian_iff_of_affine_openCover` supplies the needed cover equivalence, and that `isLocallyNoetherian_of_isOpenImmersion` plus the opens instance supplies preservation by open subschemes. No proof steps are present because this is a definition node, so `citations.json` is empty. I corrected the imported metadata by filling `same_as` with `[]`, adding the scheme dependency, adding all executed Mathlib searches with their actual results, and changing the status to `split` with a theorem-level Mathlib candidate.

## What could not be finished

Nothing remains for this split. A later worker should run the repository's dry-run delivery checks.

## Second reading by H1

- Item statement: checked the blueprint node against Stacks `morphisms.tex`, Tag 01T6 (`lemma-finite-type-noetherian`) and Tag 01T5 (`lemma-immersion-locally-finite-type`), hypothesis by hypothesis; retained as correct.
- Item proof steps: there are no proof steps for this definition node; no uncited dependency or elementary-step issue applies.
- New nodes: none were created, so B1-B7, duplicate checks, and per-node edge-case checks are vacuous.
- Mathlib candidate: reran LeanFinder, Loogle, and grep; `IsLocallyNoetherian`, the affine-cover equivalence, and open-immersion preservation are present in `Mathlib/AlgebraicGeometry/Noetherian.lean` at lines 57-59, 131-135, 151-155, with the opens instance at 158-159, but the Stacks definition agrees through theorems rather than by definition.
- Edge cases: the affine-cover definition is valid for the empty scheme (empty cover), a field spectrum (one affine with a Noetherian field), and arbitrary affine schemes; the open-subscheme clause specializes correctly to the empty open and to the whole scheme.

Changes made in this second reading:

- Replaced the node's stale Mathlib search summaries with the exact successful searches recorded in `searches.jsonl`, including the declarations and source lines read.
- Added the Stacks labels to both external source entries, so each source is identified by tag and label.
- Added this independent second-reading audit and recorded that no proof or new-node repairs were necessary.
