# lem-tw-multiplicativity — Q89

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-tw-multiplicativity.json`: item, statement, status split; the scalar product and inverse identities are proved in two elementary steps, using existing Mathlib leaves. No new nodes, no new Mathlib leaves.
- `citations.json`: exact statement excerpts for both dependencies of each proof step.
- `report.md`: this report. `searches.jsonl` contains the six real search-command records, retained without modification.

## Attachments

None. Searching the whole project `WeilConjectures/` for the item id and its blueprint tag found no declaration. Concept searches found `AlgebraicGeometry.WeilGroup.frobeniusWeight_mul` and `AlgebraicGeometry.WeilGroup.frobeniusWeight_inv` in `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Operations.lean:57,83`. I read their complete proofs and the definition `frobeniusWeight` in `RealSheaves/Weights.lean:61`. They are sorry-free locally, but their statement uses the logarithmic complex-embedding weight, whereas the imported item refers to an impossible ell-adic normalization. Thus they are useful corroboration, not an exact attachment for the imported assertion. The corrected equation formulation is proved here directly, without importing the logarithm-to-real-power equivalence or relying on a transitive sorry audit.

## WANTED

None. All sources used are already available. No SGA source was used.

## Source error — STATEMENT-DISPUTED

The imported item (both the older master and current main-20261015 text) refers to `def-tw-eigenvalue`, which asks for the Q_ell-adic valuation normalized by v(q)=1 when q=p^a and ell differs from p. Such a normalization does not exist: q is an ell-adic unit, so every rescaling of the ell-adic valuation still has v(q)=0. For an explicit small case take p=q=2, a=1 and ell=3. The usual 3-adic norm of 2 is 1, and its reciprocal is still 1, not 2. By contrast, every complex field embedding fixes 2, so |iota(2)|=2, giving the intended weight 2. This is a failure of the imported meaning, not a counterexample to multiplicativity of genuine absolute values.

The intended interpretation is fixed independently by the unit `sk-r-real-linear` (inverse weights for wt_{iota,q}), the formula 2 log |iota(alpha)| / log q in current `sk-d-real-weights/_section.md`, and the pure-weight equation in `def-weil-frobenius-module-weights`. I therefore repaired only this item: explicitly fix a complex field isomorphism, define the scalar weight by |iota(gamma)|=q^(w/2), and retain the sum and negative conclusions. Real w is the convention of the unit and the existing module-weight definition; it includes the imported integral case and makes the lemma usable for its real-weight callers. The unnecessary eigenvalue restriction is expressed as an immediate particular case: the calculation is about scalars, and does not assert that a product of eigenvalues of one operator is again an eigenvalue of that operator. No tensor-spectrum lemma is hidden here.

Removed the invalid statement/proof dependency `def-tw-eigenvalue` and replaced it with the existing module-weight convention, complex absolute value, and real power nodes. I did not edit the independently owned erroneous definition or any target. Its owner/maintainer needs this normalization report. No unit or chapter route is replaced: the repair follows the unit's own complex-weight convention, and the two elementary norm calculations are exactly the blueprint's two calculations. The item is not the key node of its unit, so no unit realization record is written.

## Searches and reuse

I searched the DAG and the whole blueprint using `blueprint_refs.py search` for `weight`, `multiplicativ`, and `weight character`, and searched DAG text for norm/power identities and scalar/tensor/inverse weight phrases. The item's blueprint ancestor is itself. The weight-character nodes concern representation data; `p-real-operations` identifies local characteristic polynomials, `lem-tw-dual-negation` concerns sheaf duality, and the tensor/determinant nodes concern spectra or determinantal weights. None duplicates this scalar calculation. The two existing Mathlib leaves `def-weil-complex-absolute-value` and `def-weil-real-power` provide exactly the elementary identities needed; no new node is justified. The item has no equivalent blueprint statement to list in `same_as`.

Six searches were run through `msearch.py`, read, and recorded exactly: LeanSearch, Loogle, two differently phrased LeanFinder queries, a broad source grep, and a targeted real-power grep. All services were available. LeanSearch/Loogle found norm multiplicativity; source hits also include norm_inv and Real.rpow_add/rpow_neg, while the semantic queries returned height, product-formula and absolute-value facts rather than this full weight assertion. I read Complex.norm_mul at Mathlib/Analysis/Complex/Norm.lean:73, norm_inv at Mathlib/Analysis/Normed/Field/Basic.lean:77, Real.rpow_add at Mathlib/Analysis/SpecialFunctions/Pow/Real.lean:207 and Real.rpow_neg at line 259. These are constituent identities, not a declaration of both weight clauses under the coefficient conventions. No new Mathlib leaf is needed: the existing two leaves already state the required multiplicativity and power-addition law. The inverse calculation is written out from these statements, rather than claiming that the absolute-value node explicitly states norm_inv.

## What remains unfinished

Nothing in this one-level split. Repair of the separate definition is reported above and is outside this item's write scope. No Lean was written, compiled, or built. The independent maintainer review remains the normal delivery gate.

## Review by Q89

I read the item and its proof in both master and main-20261015, the current unit and real-weight definition, the chapter and unit records, the source text of the faulty normalization, and the full statements of all three nodes in the corrected statement dependency list. There are no new nodes to source or audit. I compared the coefficient assumptions: p and ell are distinct primes, a is at least 1, q=p^a>1, Qlb is an algebraic closure of Q_ell, and iota is a field isomorphism without a continuity requirement. The repaired scalar condition agrees with the existing Frobenius-module condition on each eigenvalue. No geometric, finite-dimensional or semisimplicity hypothesis enters either scalar calculation.

Step 1 takes only |zw|=|z||w| from `def-weil-complex-absolute-value` and x^(y1+y2)=x^y1 x^y2 from `def-weil-real-power`. Their actual statements say both identities, and q>1 verifies the positivity hypothesis for powers. A field isomorphism preserves multiplication by its definition. Substituting the two stated norm hypotheses and distributing division by 2 proves the displayed product formula. This is an elementary calculation, not an unnamed spectral theorem.

Step 2 uses those same actual statements. Because alpha is nonzero, alpha^(-1) alpha=1, and applying iota and multiplicativity gives the displayed product of norms equal to 1. The absolute-value node says that the norm on real numbers is their usual absolute value, hence |1|=1. The real-power node says the values are positive and defines x^y=exp(y log x); consequently q^0=exp(0)=1. The stated addition law proves q^(w1/2) q^(-w1/2)=1. Dividing by the positive first factor proves the inverse formula. This avoids taking norm_inv or a negative-power theorem from a node that does not state it. The quote file reproduces the exact sentences being used, checked as substrings of the current node statements.

I tested alpha=beta=1 (weights zero), alpha=q and beta=q^(-1) (weights 2 and -2), their product (weight zero), roots of unity under iota (weight zero), and scalar 2 with q=2, ell=3 (the normalization counterexample). Zero cannot satisfy a weight hypothesis because q^(w/2)>0; retaining the explicit inverse condition therefore causes no missing case. Negative and nonintegral real weights cause no change because the power law assumes only positive base. The proof is pointwise in any fixed iota; if the hypotheses are imposed for every embedding, the same two calculations apply to each embedding. Restricting to a coefficient subfield does not alter the calculation.

Against delivery-errors B–E, I checked self-contained object introductions and real TeX, all citation statements rather than their proofs, no unrecorded non-elementary fact, no new elementary or duplicate node, no restatement-node hiding a clause, no cycle through a downstream purity/tensor result, and the exact positivity/nonzero hypotheses. Both steps are under 2000 characters and contain only the displayed elementary computations. No statement-only children, Stacks tags, off-unit theorem uses, or new tool-use declarations occur. The mathematical correction, removed dependency and reason for it are all explicit above rather than silent.
