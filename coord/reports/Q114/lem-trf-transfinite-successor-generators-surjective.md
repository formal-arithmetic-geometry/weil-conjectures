# Stage-1 report: lem-trf-transfinite-successor-generators-surjective

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-transfinite-successor-generators-surjective.json`: statement, split; no exact Mathlib match. Five explicit proof steps, retaining the statement and inherited blueprint ancestry.
- `citations.json`: verbatim statement quotations for the two steps citing `def-weil-pbc-direct-sum-modules`.
- `report.md`: this report. Searches are recorded by the prescribed command in `searches.jsonl` and appended to the item's existing searches.

No new nodes or Mathlib leaves were created. Every part of the argument is a direct finite-sum calculation, application of an explicit hypothesis, or ordinal induction with the cases written out.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item identifier, successor-generation wording, and transfinite-filtration wording. No declaration stating the item was found; no Lean was written or compiled.

## WANTED

None: the Stacks source used here is available locally.

## What was wrong or missing

The imported item had a statement and searches but no proof. Its generalization of Tag 058V to possibly noninjective maps is valid: the image induction uses only successor generation, not the splitting or injectivity used later in the source to prove injectivity. No statement dispute or statement correction is necessary. The existing ancestry goes through the older imported local-term proof into Kaplansky dévissage; I preserved it and read the current blueprint at `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/lem-trf-local-term-locality.proof.md`, as well as the chapter and unit records. This item is the algebraic image-induction tool already identified in its inherited `blueprint.from.place`; it is not a new replacement for the unit's geometric route.

The current Mathlib searches return `DirectSum.range_coeLinearMap` (Mathlib/Algebra/DirectSum/Module.lean:424) and `Submodule.iSup_eq_range_dfinsupp_lsum` (Mathlib/LinearAlgebra/DFinsupp.lean:370). I read these statements and surrounding definitions. They describe a finite-sum range as a supremum of submodules; neither identifies an arbitrary continuous ordinal filtration from successor-generating maps. The second LeanFinder phrasing instead returns adic-completion and filtered-colimit surjectivity results, whose hypotheses and maps differ. The item is therefore not an exact or one-line Mathlib specialization. All five fresh searches succeeded; the original Q80 searches remain preserved.

## What could not be finished

Nothing mathematical remains in this one-level split. Delivery checks are run after this report is written; their outcome is recorded by the delivery tool.

## Not duplicates

No new nodes. Whole-blueprint searches for `transfinite`, `successor generators`, `058V`, and `filtration`, and DAG searches for Tag 058V and successor generators found no alternative blueprint statement of this item. The existing `lem-trf-split-transfinite-module-filtration` is the stronger parent that needs this surjectivity argument together with an independent injectivity argument. The same-tag `lem-trf-filtration-successor-maps-independent` concerns injectivity/independence, not generation. Neither is cited circularly or recreated.

## Review by Q114

I read Stacks `algebra.tex`, Tag 058V (`lemma-direct-sum-devissage`), including Definition 058U and the full proof, in particular the image induction at lines 20417–20433 and its separate later injectivity induction. For the only cited node I opened `def-weil-pbc-direct-sum-modules.json` and read its entire statement: it explicitly defines finite-support families, componentwise addition and scalar multiplication, the coordinate inclusions, and decomposition as a finite sum. There are no new-node sources to review.

Step 1 uses that node's finite-support and finite-sum clauses, quoted in `citations.json`. Each supported index satisfies alpha < beta, hence alpha+1 <= beta; the assumed monotonicity puts every image summand in X_beta, and closure of a submodule under finite sums proves the required containment. Empty support gives zero, so there is no nonempty-support assumption or hidden union/supremum theorem.

Step 2 states the induction assertion, including its restricted range beta <= kappa, and proves the zero case. Its coordinate argument uses the definition of D_0 in the item's own statement: no index can be below zero, so every coordinate vanishes. X_0 = 0 is an explicit hypothesis. Ordinal induction here is the elementary least-counterexample principle for ordinals, made explicit again in step 5; no transfinite recursion construction is being assumed.

Step 3 uses the cited direct-sum node specifically for its canonical inclusion and componentwise addition; its exact inclusion clause is quoted. For a successor gamma+1 <= kappa, gamma < kappa ensures A_gamma and t_gamma exist. The successor hypothesis supplies y and b, the induction hypothesis supplies a finite-support preimage of y, and adding the single gamma coordinate produces a preimage of x with all coordinates >= gamma+1 zero. The image calculation follows the given finite-sum formula for f. This is a complete construction, not an invocation of a new successor-surjectivity lemma, and does not use injectivity or uniqueness of b.

Step 4 uses precisely continuity at a nonzero limit lambda <= kappa, an explicit hypothesis, to choose gamma < lambda with x in X_gamma. The induction hypothesis supplies a preimage supported below gamma; the coordinate definition puts that same family in D_lambda. No direct-limit theorem, preservation of colimits, bounding of an arbitrary support at a limit, or infinite sum is needed. The opposite containment has already been established uniformly in step 1.

Step 5 checks that a least failed ordinal must be zero, successor, or nonzero limit, each excluded by steps 2–4. Thus induction is set up and closed, and combining the two inclusions proves equality at every stage. Since D has only indices alpha < kappa, D_kappa = D even when kappa is zero. Only the additional stated hypothesis X_kappa = X gives surjectivity onto the ambient X.

For small cases I checked kappa = 0 (empty direct sum and X_0 = 0; surjectivity only if X = 0), kappa = 1 (the sole map generates X_1 because X_0 = 0), kappa = omega (a given element is already in some finite stage by continuity), arbitrary terminal successor and terminal limit stages, the zero ring and zero modules, and maps with nonzero kernels. None needs an additional hypothesis. Continuity is used only at nonzero limits and generation only at successors; if all t_alpha are zero, the induction correctly forces every X_beta to be zero.

Against delivery-errors B–E I checked that no node restates a clause, no definitions are used as unstated theorems, every actual citation is supported by its statement and a verbatim quotation, and no new graph edge points to the parent or a descendant. The proof has no off-unit statement dependency: its only proof node is the existing Mathlib direct-sum definition. The five steps are each below 600 characters and contain the complete elementary arguments; no long step hides an auxiliary comparison. I retained all existing source, creation, search, and blueprint fields and changed only the split fields plus appended honest current search records.
