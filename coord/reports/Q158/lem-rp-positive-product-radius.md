# Q158: lem-rp-positive-product-radius

## Files written

- `dag/nodes/sec-purity-real-sheaves/lem-rp-positive-product-radius.json`: statement, split; the statement is unchanged. Five explicit steps replace the imported paragraph.
- `dag/nodes/sec-purity-real-sheaves/lem-rp-taylor-sum-on-disc.json`: statement, Mathlib leaf, `Complex.hasSum_taylorSeries_on_eball`, `Mathlib/Analysis/Complex/TaylorSeries.lean:87` (context and full hypotheses read at lines 80–89).
- `dag/nodes/sec-purity-real-sheaves/lem-rp-nonnegative-summable-comparison.json`: statement, Mathlib leaf, `Summable.of_nonneg_of_le`, `Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean:530` (full declaration and proof read at lines 529–535).
- `citations.json`: complete verbatim statement quotations for every step/node citation.
- `searches.jsonl`: retained outputs of the prescribed search command; all searches used in the JSON records actually ran.

## Attachments

No exact attachment for the entire item. I read the complete project file `WeilConjectures/Mathlib/Analysis/Analytic/ConvergenceRadius.lean`. `PowerSeries.radius_tprod_le_radius` at line 233 proves the radius comparison for a product convergent in the coefficient topology, and `PowerSeries.eval_ne_zero_of_lt_radius_inv` at line 179 proves zero-freeness from the analytic radius of an inverse. Both proof texts are sorry-free. Neither statement starts from the item's holomorphic-function/Taylor-series assumption, and applying them still requires a Taylor-to-radius theorem. I therefore did not claim an exact attachment or introduce child nodes restating these clauses.

## WANTED

None. The blueprint and all Mathlib declaration sources used were available locally. No SGA source was used.

## Findings and changes

The imported statement agrees with the current `main-20261015` blueprint statement and is correct. The older blueprint file supplies a proof paragraph omitted from the newer per-node file; I read both, together with the chapter and `sk-p-real-rankin` unit record. The imported proof left Cauchy's estimate and the radius-from-limsup criterion uncited, then treated the polynomial assertion as a pole slogan. The split instead applies the available Taylor-summation theorem at positive real arguments and the comparison test, preserving the unit's coefficient-domination route. It proves the final assertion directly by a finite coefficient identity and a vanishing-tail contradiction. No boundary regularity, continuation principle, or general Cauchy-product theorem is hidden in that last argument.

The generic new leaves are not clauses of the item: the first concerns Taylor series of any complex differentiable function at any center, without positivity, products, or polynomial inverses; the second concerns summable real sequences, without power series or radii. Both have statement-only records, empty proofs, and exact Mathlib matches. The item carries the actual coefficient and inverse-polynomial arguments.

Whole-DAG and whole-blueprint searches included radius, Taylor, Taylor series, Cauchy, Cauchy product, absolutely convergent, summable, comparison test, dominated, and convergence. Declaration-name searches found no existing node stating either new leaf. The definition nodes `d-real-series` and `sk-d-real-series` define radius rather than prove either theorem. `lem-wf-boundary-semicontinuity` and `lem-rp-upper-bound` contain analytic reasoning in their proofs but their statements concern sheaf weights, so their proof text supplies no usable analytic statement. Searches of the project Lean source found only applications of the generic comparison test, not a project declaration stating the new leaf. The recorded `FormalMultilinearSeries.pi` and `.prod` search hits concern Cartesian products of vector-valued series, not the scalar product in this item; they are not matches for it.

## Not duplicates

- lem-rp-taylor-sum-on-disc vs lem-rp-positive-product-radius: Taylor summation on a disc is a general analytic input with no positivity or product-radius conclusion.
- lem-rp-nonnegative-summable-comparison vs lem-rp-positive-product-radius: comparison of real summable families is a general sequence theorem, without formal products or radius conclusions.
- lem-rp-taylor-sum-on-disc vs d-real-series: the former proves Taylor convergence; the latter defines a convergence radius and formal products.
- lem-rp-nonnegative-summable-comparison vs d-real-series: the former proves a summability implication; the latter only defines series notions.

No new node has a Stacks tag, and no existing node with a matching analytic statement was found.

## Unfinished work

None in this stage-1 split. No Lean was written or compiled. Independent maintainer review and later formalization remain the normal project process.

## Review by Q158

I read the item's older blueprint statement and complete proof, the current main-20261015 statement, `dag/chapters/sec-purity-real-sheaves.json`, and both unit proof steps in `dag/units/sk-p-real-rankin.json`. This lemma supplies the nonnegative-product comparison in unit step 1 and the reciprocal-polynomial zero-freeness used in step 2. The replacement of Cauchy estimates by Taylor convergence is entirely below those steps and preserves their conclusions. The item is not the unit key node, so I changed no unit record.

For step 1 I reopened `d-real-series`: its statement explicitly requires degreewise local finiteness and defines coefficientwise products. A finite set of relevant factors gives the coefficient by a finite expansion. Selecting degree n in factor j and zero in all others contributes exactly a_{j,n}, including n = 0, and every other term is nonnegative. No analytic theorem is used here.

For step 2 I read `Complex.hasSum_taylorSeries_on_eball` and its surrounding variables, including completeness, differentiability on the open disc, and membership of the evaluation point. The new Taylor node says precisely that the coefficient family sums to the function value. I specialize the codomain to the complete space C, the center to 0, and the point to real t with 0 ≤ t < R. The item's Taylor hypothesis identifies its coefficients with h^(n)(0)/n!. Applying the continuous real-part map to finite partial sums gives summability in R, so no absolute-convergence theorem for general complex Taylor series is assumed. Positivity comes from step 1. Boundary continuity is unnecessary.

For step 3 I read the exact statement and proof of `Summable.of_nonneg_of_le`. Its lower sequence must be nonnegative, its upper sequence must already be summable, and domination must hold at every index. These hold for a_{j,n}t^n and A_nt^n by steps 1–2 and t ≥ 0. The radius definition in `d-real-series` is exactly convergence of the absolute coefficient series at every smaller nonnegative real argument. Thus this step gives the desired bound directly, without a root test. The comparison node introduces both real coefficient sequences using the formal-series convention in d-real-series. Its match specializes the arbitrary Mathlib index type to N and g = u, f = v in one line. Both new leaves cite the formal-series convention, and their numeric match.line fields record the inspected declaration lines.

For steps 4–5 I checked the polynomial clause directly, using only the coefficientwise product convention in `d-real-series`, finite sums, and convergence of the real nonnegative series already proved in step 3. For N ≥ d the coefficient equations give the exact finite identity 1 = sum_{k=0}^d p_k z^k s_{N-k}(z). If P(z) = 0, subtracting P(z)s_N(z) and taking norms bounds 1 by a finite sum of tails of the convergent real series sum b_n |z|^n. Every fixed-length tail tends to zero as the difference of partial sums with the same limit. This gives the contradiction without assuming a general Cauchy-product theorem or constructing an infinite complex sum. The k = 0 tail is empty, and choosing N ≥ d ensures every N-k is nonnegative. This is one routine finite identity and tail estimate; no separate analytic identification is hidden. Every step is below 2000 characters.

I tested empty J (the conclusions are vacuous), one factor (coefficient domination is equality), factors equal to 1, degree zero, z = 0, P = 1, R = 0 (empty disc), and R = infinity. The leaves also handle an empty disc and an empty index set. No positivity assumption is needed on a polynomial's own coefficients; it is imposed only on its inverse series as in the original statement. I checked delivery-errors B1–B10: self-contained new statements, actual searches, exact match files and lines, no duplicate definitions, and complete blueprint origins. For C1–C8 I checked each cited statement against its use, complete proof-dependency unions, and no reverse reference from either new leaf. For D1–D5 the actual argument stays on the item, and the leaves are generic Mathlib results, not shifted conclusions. For E1–E7 I verified hypotheses, finite-sum indices, endpoint cases, and that no statement correction is required. The quote file copies each cited statement literally.


## Dry-run repairs

The first dry run rejected the two leaves for missing definition citations and missing numeric `mathlib_match.line` fields. Both leaves now explicitly cite the formal-series convention in `d-real-series`, and the line fields are 87 and 530. The comparison leaf specializes the arbitrary-index Mathlib theorem to coefficient sequences indexed by N. I also replaced the final complex infinite-sum argument with the finite-tail contradiction explained above, so no auxiliary absolute-convergence theorem is needed.
