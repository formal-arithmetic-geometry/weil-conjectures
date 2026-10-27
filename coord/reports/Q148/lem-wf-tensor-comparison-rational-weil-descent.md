# Stage-1 report: lem-wf-tensor-comparison-rational-weil-descent

## Files written

- dag/nodes/sec-six-functors/lem-wf-tensor-comparison-rational-weil-descent.json: statement split into six explicit elementary steps; no exact Mathlib match.
- citations.json: nine verbatim statement excerpts, one for every step/node citation.
- report.md: this report. The five Q148 search calls are recorded by msearch.py in searches.jsonl.

New nodes: 0. Mathlib leaves: 0. The existing conditional hypotheses leave only elementary fraction and composition calculations; introducing nodes for those would violate the elementary-node rule.

## Attachments

None. Searched the complete project WeilConjectures source for the exact blueprint docstring tag and the tensor-comparison/rational-Weil notions, including WeilObject and WeilSheaf. No declaration states all clauses of this item. The Mathlib tensorBifunctorIso hit is not a project attachment.

## Literature

No WANTED sources. Read the current blueprint source literature/blueprint/main-20261015/blueprint/sec-six-functors/sk-rem-sf-pf-done/fix-prop-projection-formula.proof.md, especially its penultimate sentence, and the chapter/unit records. That sentence supplies the intended equivariance obligation, not this detailed denominator argument. The proof is therefore honestly marked agent-written. This item isolates the formal rational/common-stage conclusion of its parent's Step 5; it does not reprove the analytic or integral completion assertions.

## Corrections and limitations

The imported statement contained literal doubled TeX backslashes. Normalized these to single TeX backslashes, as required by B4; no hypothesis, object, equality, or conclusion changed. There is no mathematical STATEMENT-DISPUTED issue. The integral tensor bifunctors, the actual completion-unit natural isomorphism, and the integral Frobenius square remain explicit assumptions. In particular this proof supplies no comparison between components at different fields without transition identifications.

Retained the five inherited Q140 Mathlib search records, including the explicitly invalid and superseded Loogle query. Added exactly the five Q148 calls made through msearch.py: LeanFinder twice with different descriptions, LeanSearch, Loogle, and grep. Read their hits and the source of Mathlib/CategoryTheory/Localization/Monoidal/Basic.lean:120–146 and Localization/Construction.lean:260–290. The first constructs the tensor induced from one monoidal localization; the second extends natural transformations across a categorical localization. Neither states this item about two prescribed tensor bifunctors, completion-unit components, rational Frobenius maps and common-stage Weil morphisms. Module localization and adic-completion hits are ingredients with different objects, not one-line specializations proving the item.

## Not duplicates

No new node pairs. The DAG and blueprint searches found the existing def-wf-tensor-product and the related lem-sf-completed-tensor-rational-naturality, lem-pur-semilinear-scalar-localization, lem-sf-tensor-comparison-localization-descent and lem-pur-rational-weil-naturality-mate. I read their statements. The first two general tools do not directly state this conditional comparison between ordinary and completed tensor. The tensor-comparison localization node concerns a symmetric monoidal realization into perfect complexes with coherent coefficient transition tensorators. The purity mate node concerns a smooth purity comparison. None is duplicated or needed as a black box: the item's given bifunctors and integral square allow the shorter explicit arithmetic calculation. Blueprint searches for rational Weil, tensor comparison and completion Frobenius found no blueprint node exactly stating this item.

## Review by Q148

I checked B–E against the node, the source and the exact statements of all five nodes cited in the proof. There are no new statement-only nodes to validate or source separately, no unrecorded Stacks-tag invocation, no SGA source and no Lean writing or compiler call. The chapter and unit route stays the projection transformation's Weil equivariance. This is a formal conditional descent, so the fact that its proof only cites definitions is justified by the explicit integral hypotheses: it does not attempt to infer completion, constructibility or a canonical pullback square from a definition.

Step 1 uses def-weil-linear-scalar-localization's actual localization functor, which preserves the two assumed integral inverse identities. Step 2 uses def-weil-pbc-rational-category's exact Hom tensor formula, def-weil-l-adic-coefficient-extension's decomposition of every nonzero scalar as a unit times an integer power of the uniformizer, and def-weil-linear-scalar-localization's bilinear composition. A finite sum has a common power denominator. Dividing the integral naturality equality by the product denominator proves naturality on every rational pair of arrows. This requires neither torsion-free integral Hom groups nor cancellation in them; tensor actions on fractions are hypotheses of the item. These statements were opened and their verbatim clauses are in citations.json.

Step 3 uses def-wf-weil-category's completed integral coefficient transport followed by rationalization and the localization functor of def-weil-linear-scalar-localization. The square is assumed at the integral stage and is simply mapped into the rational category. Step 4 then substitutes the two arbitrary rational Weil isomorphisms into Step 2 and the equation from Step 3; def-wf-tensor-product states the typed pullback-comparison-then-tensor composite used for the tensor Frobenius. No claim that an integral numerator is invertible enters this calculation.

Step 5 uses precisely the commuting-morphism equation in def-wf-weil-category. Multiplying the square by the component inverse on the left and its Frobenius image on the right gives the reversed square; functoriality supplies H(chi) H(chi inverse) = 1. Thus both maps are Weil morphisms and their composites are the actual identity arrows. Step 6 uses that same definition's transition formula and common-stage composition rule. The tensor objects being compared are both represented at the chosen field L, so their comparison and inverse compose at that same field to [L,1]. The identity-field case uses the supplied unit identifications. This does not hide an assertion of field-independence of untransported components. All of those clauses are included verbatim in the step-6 quote.

Small cases checked: a zero tensor object or the empty scheme gives the unique zero-object identity; zero numerators and denominator exponent zero satisfy the same calculation; replacing a numerator/denominator by an equivalent fraction changes neither side since the tensor actions are already well-defined bifunctors. Multiplication by the uniformizer on a rank-one integral coefficient object is a rational isomorphism with a noninvertible integral numerator, and the argument still applies. An arbitrary nonzero slope therefore needs no invariant integral isomorphism. Inputs already at one field satisfy the L=E=F clause. Each step is below 600 characters, contains its actual calculation, and hides no long lemma. No parent or descendant theorem is used to prove the item, hence no circular dependency is introduced.

## Unfinished work

None in this stage-1 split. The independent maintainer review remains to be done after delivery.
