## Worker report

Item: lem-trf-exact-block-coefficient-projection. Group Q21. Stage 1 only, 2026-10-23. Direct delivery with self-review, as required by the dispatch brief.

## Files written

- dag/nodes/sec-trace-formula/lem-trf-exact-block-coefficient-projection.json: statement unchanged; eight proof steps, five distinct cited nodes, status split, proof origin agent, inherited searches retained and actual new searches appended.
- dag/nodes/sec-trace-formula/lem-trf-shift-filtered-matrix-inverse.json: one new statement-only algebra lemma, status unsplit, no Mathlib match. Its statement is about inverse matrix support, not projections, generator replacement, or derivative equations. The proof suggested below is retained here for its next worker.
- citations.json: a verbatim statement quotation for every cited node in every item step.
- searches.jsonl: the actual msearch records, read before verdicts were written. prepare.py is sandbox-only preparation, not a delivery file.

One new node, zero new Mathlib leaves. No Lean file, compiler, Lake, build, repository write, or manual git operation was used.

## Attachments

None. I searched lean/WeilConjectures for the item id and blueprint tag, block/coefficient projections, supported division, shifted matrix filtrations and their expected names. There is no declaration stating the item. The full source library was also searched for the new lemma before creating it. Unrelated derived coefficient projections do not concern formal coefficient elimination. A declaration merely carrying sorry would not qualify.

## Sources and WANTED

I read the current literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/_section.md and lem-trf-local-term-locality.{md,proof.md}, as well as the chapter and unit records and the item's ancestry through regular-hilbert-coefficient-data. The current blueprint's contracting-correspondence proof does not itself contain this formal algebra subargument. I retain the historical ancestry already assigned to this branch and make no change to the unit, chapter, or their route.

I read ILO, Travaux de Gabber, VIII 2.3.11--2.3.13, printed pp.93--94 (PDF pp.99--100). These are the reference route for the characteristic-zero desingularization input, not a source asserting our matrix support lemma. I read Bierstone--Milman, Canonical desingularization in characteristic zero, Invent. Math. 128 (1997), Lemma 9.12, formula (9.13), and Definition 9.14, printed pp.280--281, online at https://mahalex.net/seminars/gabber/Bierstone-Milman%20Canonical%20desingularization%20in%20characteristic%20zero.pdf (PDF pp.74--75). The finite solve there explains regularity after a determinant is inverted and subtraction of the full generator multiples. The simultaneous old-test projection and the shifted support estimate are explicit agent refinements; proof_origin is therefore agent. No SGA is cited or used.

WANTED: local copy of Bierstone--Milman 1997, Lemma 9.12 and Definition 9.14, pp.280--281, for this item and lem-trf-shift-filtered-matrix-inverse. The online source was read; nothing was downloaded into the repository. No Stacks tag states this formal normalization package, so no unrelated tag has been substituted for the actual source.

## Searches and Mathlib assessment

Before creating the new lemma I searched the whole DAG for matrix inverses, filtered inverse matrices, shifted degree-lex support, cofactors, coefficient elimination, triangular formal matrices, initial exponents, and the proposed id. I ran tools/blueprint_refs.py ancestor on the item and search on coefficient projection, first exponent, matrix inverse, shifted, and cofactor, across all imported chapters. The inverse-matrix search returns only the general-linear-group definition; the coefficient search returns unrelated derived functor projections. No blueprint node states our support inequality. The new node's ancestry prepends this item to the existing via list, and its place identifies the inverse matrix estimate serving the recorded local invariant branch. same_as is empty for both nodes.

Every recorded new search ran through the required msearch.py command; the exact query, service result and verdict are in the node and searches.jsonl. Both the item and the new lemma were searched in a second semantic phrasing. LeanFinder's second phrasing for the new lemma returned Matrix.blockTriangular_inv_of_blockTriangular. I read Matrix/Block.lean:407--433: this theorem preserves entries that are identically zero in a block pattern, not inequalities on the individual W coefficients with row and column exponent shifts. It is not a one-line specialization. Scalar MvPowerSeries.inv, invOfUnit, coeff_inv and isUnit_iff_constantCoeff concern one scalar series. I read MvPowerSeries/Inverse.lean:125--144 and Matrix/NonsingularInverse.lean:170--217. The matrix inverse and adjugate APIs give inverse identities, but not the required shifted support estimate. Loogle Matrix.inv, MvPowerSeries gave no hits, and the source grep for shifted filtration/inverse support gave none. These services were available, so no unavailable result is disguised as a negative one.

## Not duplicates

lem-trf-shift-filtered-matrix-inverse vs lem-trf-exact-block-coefficient-projection: the new lemma states only a support bound for an arbitrary invertible matrix over a formal series ring with finitely many exponent weights. It has no diagram, old projection, correction column, coefficient scheme, kernel, or generator family. Steps 1--5 and 7--8 still construct and prove the actual projection; step 6 uses the bound to justify the full correction's leading order.

lem-trf-shift-filtered-matrix-inverse vs lem-weil-pbc-matrix-adjugate-identity: the existing Mathlib leaf gives the two adjugate identities and the cofactor formula. It says nothing about monomial supports or shifted order. I cite it directly for the ordinary inverse identities rather than duplicating them.

lem-trf-shift-filtered-matrix-inverse vs lem-sfb-matrix-cramer-determinant-identities: that existing leaf concerns determinant multiplication, the determinant of the adjugate and column replacement. It has no coefficient support condition or conclusion. No new node shares a Stacks source tag with an existing node.

## Argument retained for the new unsplit lemma

Let theta(delta,u) be (|delta|+|u|, delta_1,...,delta_m,u_1,...,u_n), compared lexicographically in the ordered abelian group Z^(1+m+n). Using the group, rather than subtracting natural exponents, avoids an illegal cancellation in N. The hypothesis says that a monomial W^delta in A_ij has theta(delta,0) >= theta(0,u_j)-theta(0,u_i).

Since det A has nonzero constant coefficient in a field, it has a scalar formal inverse: its constant coefficient is inverted in L, and the coefficient in each positive total degree is determined recursively from (det A)d=1 using only already determined smaller degrees. Commutativity gives the other inverse identity. The existing adjugate identity then constructs A^{-1}=d adj(A) and proves uniqueness by multiplying a competing inverse.

For (A^{-1})_ij the cofactor deletes row j and column i. Any monomial in a product contributing to that cofactor chooses every remaining row and column once. Adding the support inequalities gives theta(delta,0) >= theta(0,u_j)-theta(0,u_i), because all other weights cancel. Finite sums cannot introduce a monomial below this bound. Multiplication by the scalar inverse d also cannot introduce one: every W monomial has nonnegative theta(delta,0). This proves exactly the displayed conclusion. The empty inverse matrix is handled separately, without a cofactor of size -1. This is a complete suggested proof for a future split, recorded only here; the new node itself contains no proof or proof dependencies.

## Review by Q21

I checked the split with the item, the new node, the cited statements and the sources open. The item statement is byte-for-byte unchanged. No statement dispute was needed. In particular I retained the reviewer's important distinction that only i <= s_l have purely transverse vertex exponents; the later vertices may still use coefficient coordinates W. No stronger normalization of all vertices was silently assumed.

Step 1 uses the exact generated-diagram and first-dividing-vertex quotient-support definitions in def-trf-supported-homogeneous-division. Its statement says both what the generated orthants are and how Delta excludes earlier vertices. The unique pair for E and the old-test admissibility of T^gamma follow directly. The product is embedded in the actual variable order; I did not put newly essential variables on the wrong side of the old final segment.

Step 2 uses the Cauchy product in def-weil-pbc-multivariate-power-series for the monomial shift. Everything else is a stipulated property of P^-. I checked that gamma passes every earlier test before applying its first-exponent hypothesis. Merely preserving the exponent would not immediately justify diagonal coefficient 1, so I added the explicit argument subtracting r T^gamma with r=[T^gamma]C_gamma. This monomial is fixed by P^- because it is in the old kernel. A different diagonal value would contradict first-exponent preservation on G_gamma-r T^gamma. No arbitrary residue-field coefficient has to be lifted to R.

Step 3 quotes the actual permutation determinant formula in def-weil-pbc-matrix-determinant and both inverse identities from lem-weil-pbc-matrix-adjugate-identity. I opened both statements; the latter applies over arbitrary commutative coefficient rings and includes empty matrices, and is already a Mathlib leaf. Triangularity at a follows from step 2, the determinant is 1 at a, and adjugate divided by that one determinant is regular on the single required open. This uses neither a uniform determinant for infinitely many jets nor a second shrinking for the tails.

Step 4 is the explicit identity v(G-Cc)=v(G)-Bc and the elementary old-kernel check. Old tests are R-linear even when their values are full series in the complementary variables. For a forbidden degree <= Q exponent lying in the old product diagram, its old-coordinate degree is <= Q, so the old tests actually do kill it. This verifies the crucial hypothesis hidden by a bare assertion that the tests are equivalent. Idempotence follows by applying the same formula to an element already in the common kernel.

Step 5 substitutes the full difference C_gamma-T^beta f_j in the old ideal and writes P_l H-H explicitly as an unchanged-prefix combination. No assertion about truncated ideals is used. Regularity was already obtained in step 3, and all columns are retained in their entirety.

Step 6 is the sole use of the new support lemma. I checked its indices: the inverse entry is indexed (gamma,eta), hence it takes a term at eta to one whose shifted exponent at gamma is at least as large. Taylor expansion of B at a meets the support hypothesis because the full C_gamma starts at (0,gamma), not merely because B(a) is triangular. The determinant constant is 1. The input coefficient terms are strictly later than mu since the leading monomial passes the selected tests. Adding the inverse support inequality and then the column's support inequality keeps them strictly later. Thus the correction cannot cancel or precede the first exponent. This writes out the compatibility that a phrase such as 'triangular elimination preserves order' would otherwise hide.

Step 7 checks that the later minimal vertices are outside every prefix orthant even if they have W components, and applies step 6 only after that check. The unchanged first s_l generators make both ideal inclusions explicit. Earlier vertex derivative equations and Jacobians are formed from these unchanged generators, so their functions and all their derivatives are literally unchanged; I did not claim that arbitrary derivatives of changed generators are identical. These are the earlier derivative equations meant by the block induction in the parent statement and BM's construction.

Step 8 uses the same determinant definition for the empty case. Empty E means the old tests already cover the current bounded tests. All operations are finite in the column index, and commute with coefficient extension; a coefficient equal to 1 remains nonzero in every residue-field extension. First exponents in these assertions are only claimed for nonzero series. I checked Q=0, Q below the current degree, l=1, the empty old prefix, no transverse variables, E empty, and an unchanged prefix of length zero. For the new lemma I tested r=0 (det=1), r=1 (only a scalar inverse), m=0 (ordinary triangular matrix inversion), repeated weights, and a two-by-two matrix [[1,W],[1,1]] with transverse weights 0 and 1; its inverse over L[[W]] respects the same shifted bounds. There is no characteristic-zero restriction on the new algebra lemma; the item's characteristic zero remains exactly as given.

B1--B10 were checked against the actual files: the only new node is self-contained, statement-only, uses existing field/matrix/formal-series/determinant definitions, has single TeX escaping, introduces no invented Stacks attribution, records genuine searches and no false Mathlib leaf, has complete blueprint ancestry, and has no project attachment. C1--C8 were checked through the statement quotations and the step readings above: the one substantive support fact is a cited node, while the kernel/ideal computations remain elementary steps; no proof internals of another node are used. The adjugate tool is a preexisting Mathlib leaf, so no off-route theorem is imported. D1--D5 were checked by leaving the actual projection construction in the item and extracting only the general matrix support lemma. E1--E7 were checked in the explicit hypotheses, coefficient order, strict inequalities and edge cases above. Every step is shorter than 2000 characters. Nothing is left unfinished beyond the intentionally unsplit new lemma.

## Validation

Server review_split and the required deliver.py --no-push are used for validation; no local check_dag, review_split or preflight script is run. Final results are recorded after those commands exit.

Server review_split exited 0 with PASS. The required delivery dry run exited 0 with `OK (not pushed)` at e689cb85847 and `preflight passed`; this includes the server's DAG and split checks. The subsequent delivery command validates the packaged files again before pushing.
