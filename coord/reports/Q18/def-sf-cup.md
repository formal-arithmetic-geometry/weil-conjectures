# Stage-1 report: def-sf-cup

## Files written

- `dag/nodes/sec-six-functors/def-sf-cup.json` — existing definition, now split; no new nodes; Mathlib verdict: no exact match.
- `citations.json` — empty because the definition has no proof steps.

## Attachments

None. `AlgebraicGeometry.Etale.mixedSupportCupProduct` in `WeilConjectures/SixFunctors/Etale/Derived/PoincarePairing.lean:138-145` is sorry-free and constructs the central composite, but it does not state the item’s coefficient-stage transport or associativity, unitality, and graded-commutativity clauses, so it is not an exact attachment.

## WANTED

None.

## What was checked and corrected

The item was copied from the shared DAG and checked against `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-identification/def-sf-cup.md`, the `sec-six-functors` chapter, and unit `sk-thm-sf-identification`. Its dependencies were retained: `def-sf-datum` supplies the six-functor operations, adjunction counit, and projection transformation, while `def-weil-derived-tensor` supplies the derived tensor. I recorded the current blueprint order and marked the node `split`; the analogous `def-pod-mixed-support-cup-product` blueprint node is listed in `same_as` but fixes the Poincare setting and adds an explicit right-support convention and coefficient-change wording, so it is not a duplicate replacement.

## Not duplicates

- `def-sf-cup` vs `def-pod-mixed-support-cup-product`: the existing node is the product in the fixed Poincare-duality setting at all four coefficient stages and includes an explicit right-support symmetry plus separate coefficient-change claims; this item is the generic six-functor datum definition over all four coefficient stages and has the projection/counit composite and coherence wording of the current `def-sf-cup` blueprint node.

## Review by Q18

I read the project source declaration and verified that its type is the mixed-support map obtained by the projection transformation for `Ra_!` followed by `Ra_!` applied to `1_K` tensored with the counit of `La^* ⊣ Ra_*`; this matches the composite in the item. I also checked the source docstring and confirmed that the declaration does not assert the item’s stage transport or coherence properties, which is why I did not attach it. After the first dry run identified the standalone-node wording rule, I replaced the opening “In the setting of” phrase by an explicit fixation of the datum, morphism, point, coefficient stage, and RΓ notation. There are no proof steps and hence no cited-node quotes. I searched the whole DAG and blueprint for the cup-product statement, projection-map terminology, and the analogous `def-pod-mixed-support-cup-product`; no separate node states the generic item. The required leanfinder, loogle, leansearch, and Mathlib grep searches (including second phrasings) found no exact Mathlib declaration; generic adjunction and underived sheaf hits were recorded as generalizations. Edge cases checked from the definition are that the counit has source `La_X^* Ra_{X*} L`, the projection map has target `Ra_{X!}(K ⊗^L La_X^*Ra_{X*}L)`, and the final map lands in `Ra_{X!}(K ⊗^L L)`; no extra hypothesis was introduced.

## Unfinished

The first worker left no open implementation work; the independent second reading and delivery dry run are recorded below.

## Second reading by Q18

- Item statement: checked against `literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-thm-sf-identification/def-sf-cup.md` (node `def-sf-cup`, order 2528) and `PoincarePairing.lean:123–145`; the displayed projection/counit composite now has the correct second projection input `Ra_{X*}L`, and the four coefficient stages and coherence clauses agree with the blueprint.
- Proof steps: none (statement-only definition), so there are no cited proof steps or elementary-step verdicts.
- New nodes: none; the item’s two statement dependencies are existing definition nodes, and the `def-pod-mixed-support-cup-product` search result is a distinct fixed-setting formulation rather than a duplicate.
- Mathlib/Lean search record: reread all entries in `searches.jsonl`; they report no exact declaration, only generic adjunction, monoidal, and underived sheaf results, so no Mathlib leaf is available.
- Edge cases: the empty scheme and zero complexes give the zero composite; for a field coefficient stage the same two arrows are defined; (n=1) is the residue-field stage, while (n=0) is outside the datum because (n\ge1), so no unlisted case is silently admitted.

## Source error

`STATEMENT-DISPUTED`: the imported sentence saying that the projection transformation is applied to the pair `(K,L)` is ill-typed: that transformation for (Ra_{X!}) takes its second argument in the point category (D(s,\Lambda)), whereas (L\in D(X,\Lambda)). The source implementation (`mixedSupportCupProduct`, `PoincarePairing.lean:138–145`) and the Poincare pairing blueprint use (Ra_{X*}L) as the second input. The item statement was repaired to show the intermediate object (Ra_{X!}(K\otimes^L_{\Lambda_X}La_X^*Ra_{X*}L)) and the counit map explicitly; no hypothesis or conclusion was otherwise changed.

## Changes in second reading

- Repaired the item statement’s projection input from (L) to (Ra_{X*}L), with the full two-arrow composite, because the original wording was ill-typed.
- Added the independent edge-case and source-implementation checks above; no node files were added or removed, and `citations.json` remains empty because this is a definition without proof steps.
