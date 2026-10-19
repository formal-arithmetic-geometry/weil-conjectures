# Stage-1 report: def-weil-pbc-qbar-category

## Files written

- `dag/nodes/sec-proper-base-change/def-weil-pbc-qbar-category.json`: definition marked split; no new nodes and no Mathlib leaves.
- `citations.json`: empty list because the definition has no proof steps.
- `report.md`: this report.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree for the exact blueprint tag, Qbar coefficient-category terminology, scalar action, and pair-category construction. No declaration states this definition exactly, and no sorry-free project declaration was found to attach. The upstream master checkout is reference material only and is not treated as a finished proof.

## WANTED

None. The complete construction is present in the obtained blueprint source `literature/blueprint/master/blueprint/sec-proper-base-change/sk-thm-properbasechange/def-weil-pbc-qbar-category.md`.

## Corrections and boundaries

This node is a definition, so its one-level split consists of retaining the complete construction and naming the existing inputs. I retained all four statement dependencies: the finite-stage pair category supplies objects and morphism classes; common-stage cones supplies the shift and distinguished triangles; the Verdier-axiom theorem supplies the claimed triangulated-category consequence; and the Karoubi-envelope definition supplies the final comparison terminology. No clause was moved into a new node, and no proof was invented for the definition. The item remains in chapter `sec-proper-base-change` and unit `sk-thm-properbasechange`; no unit realized fields were changed.

Whole-DAG and whole-blueprint searches for Qbar coefficient category, finite-stage pair category, scalar action, common-stage cones, Verdier axioms, and Karoubi envelope found the existing definitions/theorem cited above. None is an independent duplicate of this complete definition, so `blueprint.same_as` is empty. The blueprint ancestor is the item itself, and the split report records the exact paragraph realized.

## Review by NE

I read the item source in full, including its source note and order 1311, together with the chapter and unit records. I opened every cited node: `def-weil-pbc-finite-stage-pair-category` states the finite-stage objects and eventual-equality morphism classes; `def-weil-pbc-common-stage-cones` states the inherited shift and common-stage cone triangles; `thm-weil-pbc-verdier-axioms` states the four Verdier axioms and the resulting ordinary triangulated structure; and `def-weil-karoubi-envelope` states the envelope construction used in the final qualification. These statements provide exactly the notions named by the definition, while none is used as a hidden proof of another clause.

There are no proof steps, so `citations.json` is correctly empty and no non-elementary fact is uncited. I checked the edge cases of the definition on a scalar in the base finite field (where the common-stage representative is unchanged), equal source and target stages, and a common overfield containing both stages; these are all covered by the pair-category and transport definitions. The item introduces no new mathematical proposition and has no Mathlib leaf to search. The source and statement agree clause by clause, including the explicit statement that no Karoubi envelope is taken in the definition and that idempotent completeness is recorded separately.

## Unfinished work

None for this one-level definition split. No Lean was written, and no compiler, Lake, or build tool was run.

## Second reading by NE

- Item statement: checked against blueprint `def-weil-pbc-qbar-category`, order 1311, and its source note (Stacks Tags 09BS, 09BT, 09C1, 09C7); the scalar action, finite-stage objects and morphism classes, shift, common-stage triangles, Verdier-axiom qualification, and Karoubi-envelope qualification agree clause by clause.
- Proof steps: none (this is a definition node), so `citations.json` is correctly empty and no proof dependency is hidden.
- New nodes: none; there are no new-node B1–B7 checks to perform. The four existing statement dependencies were opened and each supplies the named notion: finite-stage pair category, common-stage cones, Verdier axioms, and Karoubi envelope.
- Existing-node and blueprint checks: searched the whole DAG and imported blueprint for the qbar coefficient-category construction and its terminology; the item is the unique blueprint node for this construction, with no `same_as` match. The item's imported `blueprint.from = null` is appropriate, and its split report identifies the complete definition paragraph.
- Edge cases: scalar action over a base finite field, equal stages, and a common finite overfield all remain covered by the stated choices and inherited transport data; no empty or zero case is excluded by the definition.
- Changes made: none. The worker's node, dependencies, empty citations, and report review are complete and the dry-run delivery preflight passed.
