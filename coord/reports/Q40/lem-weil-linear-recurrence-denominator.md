files written:
- `dag/nodes/sec-zeta-weil/lem-weil-linear-recurrence-denominator.json`: statement, four-step proof, blueprint completion, and Mathlib search records; no new nodes.
- `citations.json`: verbatim citations for every node used by every proof step.
- `report.md`: this report.

attachments:
- None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, denominator/recurrence terminology, and declarations in `ZetaLinearAlgebra/RationalityCriterion.lean` and `ShiftSpan.lean`. The source has related declarations (`finiteDimensional_shiftSpan_of_forall_add_eq_zero`, `PowerSeries.tfae_exists_normalized_fraction`) but no declaration stating this item exactly.

WANTED: Bourbaki, Algèbre IV.5, Exercise 3(a), for the recurrence/rationality assertion quoted by Milne; the available Milne source states this direction without proof. The coefficient proof is supplied as `proof_origin.by = agent` following the blueprint.

what was wrong in the node, blueprint, or brief:
- The imported node was unsplit and had `blueprint.from.place` already identifying step 3 of `prop-weil-rationality-criterion`; I filled `blueprint.same_as` with `[]` after searching the complete blueprint and DAG.
- No statement correction was needed. The small edge case `d=1`, `a_0=0` gives `Q=1` and the proof reduces to eventual vanishing of `c_{n+1}`, so the indexing is consistent.
- The proof now explicitly handles all four required clauses: `Q(0)=1`, the coefficient formula below `m+d`, vanishing coefficients from `m+d`, and finite support yielding a polynomial `P`.
- Every non-elementary notion used by the steps is cited to an existing node. The steps only perform finite convolution, reindexing with `N=n+d`, and the finitely-supported-sequence definition of a polynomial, so they are marked elementary.
- Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch. `PowerSeries.coeff_mul` was found as the elementary convolution formula, but no Mathlib theorem states the full recurrence-to-polynomial result; this remains an unsplit statement node.

## Not duplicates

No new nodes were created, so there are no duplicate pairs to report.

## Review by Q40

I read the imported item, the unit `dag/units/sk-prop-criterion.json`, the chapter record, the existing proof of `prop-weil-rationality-criterion`, and the relevant source files `WeilConjectures/ZetaLinearAlgebra/RationalityCriterion.lean` and `ShiftSpan.lean`. The source declarations confirm that the surrounding Lean development uses the same normalized denominator construction, but none states this exact eventual-recurrence lemma. I also read the existing definition nodes cited in the item: `def-weil-field`, `def-weil-formal-power-series`, `def-weil-eventual-linear-recurrence`, `def-weil-polynomial-ring`, `def-weil-polynomial-coefficient`, and `def-weil-polynomial-as-power-series`.

Step 1 uses the polynomial-ring, polynomial-coefficient, and polynomial-as-power-series statements to identify the coefficients of Q and obtain Q(0)=1. Step 2 uses the formal-power-series convolution definition together with the polynomial coefficient and coercion statements to derive the exact coefficient formula, including the `min(N,d)` truncation. Step 3 uses the eventual-recurrence statement at `n=N-d`; the hypotheses `N>=m+d` imply both `n>=m` and `N>=d`, so the full d-term sum is available and the coefficient vanishes. Step 4 uses the finitely-supported-sequence description of polynomials and the injective coefficient-preserving map into power series to construct P and identify QC with P. I checked each quoted citation against the cited node text and recorded the exact sentence or formula in `citations.json`.

I ran the requested Mathlib searches before finalizing the node. The searches found only general convolution or recurrence declarations, not this theorem. No new node was necessary, and no existing node was duplicated or modified.

## Second reading by Q40

- Item statement: checked against Milne, Ch. II §27, proof of Lemma 27.9, p. 157 (the quoted Bourbaki IV.5 Exercise 3(a) recurrence criterion), and the current blueprint proof; the field, formal-series, eventual-recurrence, reversed polynomial, normalization, coefficient formula, and eventual vanishing clauses agree hypothesis by hypothesis.
- Step 1: checked the displayed definition of $Q$ against `def-weil-polynomial-ring`, `def-weil-polynomial-coefficient`, and `def-weil-polynomial-as-power-series`; the constant coefficient and all coefficients above degree $d$ are exactly as used, and the step is elementary.
- Step 2: checked finite convolution and the truncation at $\min(N,d)$ against `def-weil-formal-power-series` and the polynomial coefficient/coercion nodes; reindexing gives the displayed formula for every $N$, hence for $N<m+d$, and the step is elementary.
- Step 3: checked the substitution $n=N-d$ against `def-weil-eventual-linear-recurrence`; $N\ge m+d$ gives both $n\ge m$ and $N\ge d$, so the full $d$-term sum is present and the coefficient is zero. The step is elementary under the cited definitions.
- Step 4: checked finite support, construction of $P$, and equality through the injective coefficient-preserving map against `def-weil-polynomial-ring`, `def-weil-formal-power-series`, `def-weil-polynomial-coefficient`, and `def-weil-polynomial-as-power-series`; the step is elementary and supplies every conclusion of the item.
- New nodes: none; therefore B1–B7 and duplicate-node checks are vacuous. Existing cited nodes were located in `dag/nodes/sec-zeta-weil/` and their statements were read verbatim for `citations.json`.
- Edge cases checked: $d=1$, $a_0=0$ forces eventual vanishing and gives $Q=1$; $m=0$ makes the recurrence apply from the first coefficient; the zero series gives $P=0$; and a field has $0\ne1$, as required by the field definition.

Changes made: appended this second-reading record only. No mathematical, citation, or node repair was needed; the dry run is the required final mechanical check.


Dry run: `python3 /home/ubuntu/weil-launcher-nt/deliver.py Q40 lem-weil-linear-recurrence-denominator --no-push .` completed successfully with `OK (not pushed) ... preflight passed`.
