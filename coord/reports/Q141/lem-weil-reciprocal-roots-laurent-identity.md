# Worker report

1. **Files written.** The item file `dag/nodes/sec-zeta-weil/lem-weil-reciprocal-roots-laurent-identity.json` was split in place. No new dependency nodes were created. The item has no Mathlib leaf: the Mathlib searches found only factorization, reverse-polynomial, and multiset-product ingredients. `citations.json` records the verbatim statements used by each proof step.

2. **Attachments.** None. `Polynomial.leadingCoeff_mul_leadingCoeff_of_roots_eq_map_inv` and `Polynomial.eval_inv_mul_inv_of_roots_eq_map_inv` in `WeilConjectures/Mathlib/FieldTheory/IsAlgClosed/Basic.lean` are sorry-free, but each proves only part of this item's three-clause statement, so neither is an attachment for the item.

3. **WANTED.** None.

4. **Node and source checks.** I read the item node, the master blueprint `literature/blueprint/master/blueprint/sec-zeta-weil/sk-prop-reciprocity/prop-duality-reciprocity.md`, the current proof file, and the two slopmaster2 declarations named in the node source. The statement was kept verbatim. I also searched the whole DAG and blueprint for reciprocal-root reciprocity, root-map inversion, and the two Lean declaration names; no existing node states this item or a smaller reusable reciprocity lemma. The current blueprint ancestry is retained (`prop-duality-reciprocity`), and `same_as` is set to the empty list.

## Review by Q141

I checked the hypotheses clause by clause. The item assumes an algebraically closed field, normalized polynomials, nonzero `c`, and a reciprocal-root factorization; the factorization node supplies the nonzero roots and the displayed factorization of `P`, while the item statement itself supplies the corresponding factorization of `Q`. Step 1 cites exactly the factorization conclusion and records the nonvanishing needed for inverses. Step 2 cites the polynomial degree/leading-coefficient convention, coefficient convention, and factorization conclusion; it verifies the finite-product leading coefficient calculation and obtains `deg Q=n`, `D_P=∏αᵣ`, `D_Q=cⁿ(∏αᵣ)⁻¹`, and the nonzero/product clauses. Step 3 cites the Laurent-ring definition, the substitution convention, and the factorization conclusion; it checks the factor identity `1−αᵣc⁻¹T⁻¹=−αᵣc⁻¹T⁻¹(1−cαᵣ⁻¹T)` before multiplying. Step 4 cites the coefficient, Laurent-substitution, and rational-function evaluation conventions; it checks that evaluation at `t∈L×` is defined and rewrites the signed determinant constant as the leading coefficient. Each step is marked elementary because it is a direct finite-product or one-line substitution calculation from the cited statements and definitions.

I tested the edge case `n=0`: the empty products give `P=Q=1`, `D_P=D_Q=1`, and all three conclusions reduce to `1=1`; no positivity or nonzero-degree hypothesis was added. The source's Lean declarations were checked for exact scope and were recorded as partial attachments only in the report, not used as nonexistent DAG citations. The previous imported Mathlib search records were replaced by the seven searches actually run for this item on 2026-10-17; they found no exact Mathlib declaration.

5. **Unfinished work.** None before delivery.

## Not duplicates

No new nodes were created, so there are no new/existing node pairs to distinguish.
