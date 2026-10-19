# Worker report: lem-rp-upper-bound

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-rp-upper-bound.json`: statement; split into ten proof steps, no Mathlib match.
- `dag/units/sk-p-real-rankin.json`: only `realized` and `realized_by`, binding the statement and both unit steps to this item. The maximum-weight estimate implies the unit's current arbitrary-upper-bound form by monotonicity in the exponent; for the nonzero sheaf the finite constituent multiset has a maximum.
- `citations.json`: 23 verbatim statement quotations, one for every step/node pair.

No new nodes and no Mathlib leaves. All work is in the assigned sandbox.

## Attachments

None. I read `WeilConjectures/EtaleCohomology/Purity/RealSheaves/Purity.lean`, including `AlgebraicGeometry.WeilGroup.sq_norm_le_rpow_of_isReal` at line 554 and its upstream Rankin–Selberg proofs. Although its own body has no sorry, the compressed full slopmaster2 sorry map gives the dependency chain through `hasWeightsAtMost_of_isReal`, `frobeniusWeight_le_add_inv_two_pow_of_isReal`, and `frobeniusWeight_le_add_two_of_hasNonnegCoeffs` to `exists_eulerSeries_mul_eq_coe`, whose body is sorry. Other open dependencies also remain. It is therefore not an attachment under this brief. The source theorem uses an upper bound for all constituent determinant weights; the maximum in this item supplies that hypothesis.

## WANTED

None. The blueprint and the human-authored mathematical reference used for checking are available locally.

## Faults corrected

The imported proof had two null elementary flags, no per-step source, no Mathlib searches, and statement dependencies that did not directly name reality, the weight multiset, or the finite-field curve conventions. I supplied these and made the limiting inequality explicit. The original composition-series definition did not assert existence; step 1 now proves it by dimension induction rather than attributing that theorem to the definition. I added the exact tensor sheaf/representation equivalence to justify forming the lisse semisimplification and tensor powers, the local characteristic-polynomial interface, the flag and filtration statements to justify the top-cohomology determinant factorization, and the smooth-normal curve lemma to verify normality for the tensor-weight corollary. These are existing nodes, not new stand-ins for clauses of this item.

The statement is unchanged. For the zero sheaf the phrase "maximum of the determinant weights" supplies no number, since that multiset is empty; the proof's zero-sheaf remark simply notes that any eigenvalue assertion would be vacuous. The substantive case has nonzero rank. No maximum was assigned to the empty multiset, and no extra hypothesis was silently added.

The current main-20261015 item has the same statement but no proof text; I used the master snapshot's explicit proof, compared it with the current unit's upper-bound formulation, and retained the required ancestry and source metadata. No route involving prohibited SGA sources was introduced.

## Unfinished work

None at this split level. The existing cited nodes retain their own proof obligations.

## Searches and reuse

I searched the whole DAG and the imported blueprint for upper bounds, determinant weights, and semisimplification, and read the existing statements before using them. Additional DAG searches found the existing smooth-normal curve lemma and sheaf/representation equivalence. No auxiliary node is necessary: the finite-dimensional composition-series construction, geometric-series expansion of a finite rational denominator, root-modulus computation and final Archimedean argument are written as proof steps.

The required msearch commands were run and their logged results read. LeanSearch returned generalized eigenspaces, Lie weights and sieve weights; the first LeanFinder returned Lie weights and Selberg-sieve weights, and the second returned modular-form/Petersson, Dirichlet-series and Hermite bounds. None states a lisse-Weil-sheaf eigenvalue bound. The grep search for the project theorem names, WeilGroup and determinant-weight terminology gave zero Mathlib hits. The first Loogle query rejected the guessed name `LinearMap.HasEigenvalue`; I recorded the rejection accurately and reran it with `Module.End.HasEigenvalue`, which returned zero hits. Every query is copied exactly from searches.jsonl; no unavailable service was represented as absence.

## Tool uses

The four tool declarations in `split_report.tool_uses` explain the exact tensor sheaf/representation equivalence, normal-subgroup semisimplicity, independence of semisimplification, and smooth-curve normality. They verify interfaces or hypotheses for the original Rankin–Selberg route. They do not replace the tensor-weight, top-cohomology, trace-formula, positivity, or local-root steps of that route. These are proposed tool uses for maintainer review, not maintainer-owned `tool_uses` fields.

## Review by Q129

I read the master blueprint item in full and the current main-20261015 statement and unit; I also read Zev Rosengarten's `literature/stanford-weil2-seminar/L22.pdf`, Lemma 3.1, Definition 3.2, the positivity paragraph, and Lemma 3.3 on pages 5–6 through equation (3.1). That proof gives exactly the upper-bound half required here, with the same affine smooth geometrically connected curve, real lisse sheaf, maximal determinant weight and even tensor powers. The later exterior-power argument proves a different, stronger purity statement and is not used. I checked the hypotheses of every invoked node against its actual statement; the quotations in citations.json are whole statements so no reliance is placed on an uncited construction inside a dependency's proof.

1. Step 1 uses the exact tensor equivalence to form lisse subquotients and sums, and the two definition nodes only for the meanings of composition series and semisimplification. The existence induction decreases vector-space dimension strictly and has the zero-dimensional representation as its empty-filtration base. No Jordan–Hölder existence theorem is smuggled into a definition citation.
2. Step 2 uses the statement of p-real-operations to identify local operators, p-linear-filtration for multiplication of their characteristic factors, the reality and multiset definitions for the unchanged properties, semisimplification independence for choice independence, and normal-restriction semisimplicity for the geometric semisimplicity needed next. The normal subgroup is the geometric subgroup of the Weil group. It does not infer reality for the individual irreducible factors, which would be false.
3. Step 3 uses the tensor-operation definition and exact tensor equivalence for the tensor sheaf, then cor-mg-det-weight-finite-tensor for the weight maximum. I checked nonzero rank and positive tensor exponent, proved the tensor remains nonzero by a basis tensor, and cited lem-sc-smooth-normal for the corollary's normality hypothesis. Geometric connectedness is an item hypothesis. Its geometric representation is semisimple by step 2; no claim that an arbitrary nonsplit extension is geometrically semisimple is made.
4. Step 4 uses the top-cohomology eigenvalue lemma for precisely its logarithmic weight formula and d-real-setup for q>1 and geometric Frobenius. Division by log(q) has a positive denominator. The Tate twist contributes +2 in the squared-modulus exponent; the inverse twist was not confused with a negative contribution.
5. Step 5 uses the invariant full flag (over the algebraically closed coefficient field) and filtration determinant product, then calculates reciprocal roots explicitly. A zero eigenvalue gives a constant factor rather than a reciprocal; a zero-dimensional H_c^2 gives the polynomial 1. Neither case creates a spurious zero.
6. Step 6 uses the Euler-product corollary for the entire displayed quotient, d-real-cohom for bounded-degree local finiteness, and even-tensor positivity for nonnegative inverse-factor coefficients. The substitution by a positive integer degree preserves both positivity and constant term. The numerator is H_c^1 and the denominator H_c^2, with no swapped signs or extra H_c^0 assertion taken from a mere definition.
7. Step 7 is the explicit finite geometric-series calculation, justified on every smaller closed disc by |c_j|r<1. It obtains the Taylor series of the rational quotient without an additional comparison theorem. This is the unit's elementary Cauchy-product argument and has no independent geometric claim hidden inside it.
8. Step 8 uses exactly the final zero-freeness conclusion of the positive-product-radius statement after checking every one of its hypotheses in steps 5–7. The reasoning uses no assertion of positivity for the numerator and does not assume the global rational quotient is reduced.
9. Step 9 uses the tensor-eigenvalue clause of p-linear-spectra, not a claim about exterior powers. The eigenvalue is nonzero because local Frobenius is invertible; the closed-point degree is positive. A polar-coordinate root gives an actual zero of the local determinant, and its modulus is calculated before applying zero-freeness. Taking logarithms and multiplying by a negative number reverses the inequality; q_x=q^d is supplied by d-real-setup. Thus the exponent is beta+1/k, including when beta is negative.
10. Step 10 writes the epsilon/Archimedean contradiction explicitly. Its only inputs are the inequalities already obtained for every positive k and log(q_x)>0. It does not need purity or a preexisting eigenvalue-weight upper bound.

I tested rank one with a real Frobenius scalar (the conclusion is equality at its determinant weight), a nonsemisimple Jordan extension (local polynomials agree with its semisimplification), negative determinant weights (all logarithmic manipulations retain their directions), degree greater than one (the dth root and q_x=q^d give the stated exponent), and vanishing top cohomology (D_k=1). I also checked k=1, repeated eigenvalues and the empty spectrum case. There are no new statements to test separately. I reviewed B–E: all cited files exist, source places are explicit, statements introduce the required notions through statement dependencies, no source tag is used in place of a dependency, no new duplicate or clause-node was created, and the source route is preserved. Every non-elementary step is below 2000 characters. The only corrections made during this review were adding the explicit composition-series existence argument, the exact tensor/local-operator interfaces, and the smooth-normal citation rather than leaving them implicit.
