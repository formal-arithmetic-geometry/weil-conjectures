1. Files written:
   - `dag/nodes/sec-abelian-varieties/pqf-lem-incomparability.json`: item marked `mathlib`, with the Mathlib search record and `Ideal.IsIntegral.comap_lt_comap` match.
   - `citations.json`: empty, because the item is a Mathlib leaf and has no natural-language proof steps.
2. Attachments:
   - `Ideal.IsIntegral.comap_lt_comap` belongs to existing node `lem-weil-pbc-integral-incomparability` as the same Mathlib result.
3. WANTED: none.
4. The imported proof paragraph gives the standard localization proof. Mathlib already packages the needed implication: for an integral algebra, strict inclusion of prime ideals gives strict inclusion of contractions. Its contrapositive is exactly the stated incomparability conclusion. The existing DAG leaf `lem-weil-pbc-integral-incomparability` states the equivalent strict-contraction form, so I created no duplicate node.
5. Nothing remains unfinished.

## Not duplicates

`pqf-lem-incomparability` vs `lem-weil-pbc-integral-incomparability`: the statements are equivalent formulations of the same fact; the existing node uses an explicit ring homomorphism and strict contraction, while this item uses the shorter integral-map and equal-contraction formulation. No new node was created.

## Review by C1

I read the imported item and its blueprint proof paragraph, the chapter and unit records, and the existing node `lem-weil-pbc-integral-incomparability`. I checked Mathlib source `Mathlib/RingTheory/Ideal/GoingUp.lean` at lines 160 and 221-224: the latter assumes an integral algebra and a prime ideal `I` and proves `I < J` implies strict inequality of contractions. Applying it to the two comparable primes and taking the contrapositive gives equality when contractions agree, exactly the item statement. The Lean source checkout contains no project declaration tagged `pqf-lem-incomparability`, so there is no attachment to a project theorem. I reran the required searches with the item id: LeanFinder found the GoingUp family, Loogle had no direct hit for the queried spelling, grep found both integral contraction declarations, and LeanSearch was unavailable and recorded as such. I verified that no new proof step or citation is needed for a Mathlib leaf and that the pre-existing equivalent leaf is not duplicated.

## Second reading by C1

- Item statement: checked against the blueprint node `pqf-lem-incomparability` and the imported proof paragraph; the hypotheses are an integral map and comparable prime ideals with equal contraction, and the conclusion is equality. Verdict: correct.
- Step 1 (Mathlib replacement): checked against `Ideal.IsIntegral.comap_lt_comap` in `Mathlib/RingTheory/Ideal/GoingUp.lean:221-224` and its use of `Algebra.IsIntegral.isIntegral`; strict comparable inclusion gives strict contraction, so its contrapositive gives the stated equality. Verdict: exact specialization, with no uncited proof step.
- New nodes: none; the existing `lem-weil-pbc-integral-incomparability` was searched and recorded as the equivalent strict-contraction formulation, so no duplicate node is present.
- Edge cases checked: the zero ring has no prime ideals; for a field (including the identity integral map) the only prime is `bot`; the empty scheme contributes no affine prime pair; and the statement is vacuous for chains of length zero or one. No edge case changes the conclusion.

Changes made: retained the Mathlib leaf and its recorded searches, retained the explicit distinction from `lem-weil-pbc-integral-incomparability`, and added this second-reading audit. No node or citation file was added or needed.
