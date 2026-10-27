# Stage 1 delivery: lem-trf-coordinate-axes-normalization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-coordinate-axes-normalization.json`: split into ten proof steps, with the statement retained verbatim, complete proof dependencies and Mathlib search records. Added the existing algebra-homomorphism/quotient definition to statement dependencies.
- `citations.json`: twenty entries, one for every step/node citation, quoting the actual cited statement verbatim.
- `report.md`: this report. No new DAG nodes, hence no new Mathlib leaves. All general tools already exist in the DAG.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for multicross, coordinate axes, equal constant and same constant. No declaration states this item. The equal-constant dual-number construction is about truncated dual numbers and is not a proof for formal power series. The existing `lem-weil-pbc-power-series-normal-domain` is a usable general tool, not an attachment for the item.

## WANTED

None. Read the source locally: `literature/stacks-project/curves.tex`, Tag 0C1U (`equation-multicross`), the complete discussion before Tag 0C1V (`lemma-multicross-algebra`). This item uses arbitrary fields and b >= 1 as in the discussion, not the separably closed/reduced Nagata hypotheses of the subsequent lemma. Also read `algebra.tex`, Tag 0306 (`lemma-Noetherian-power-series`) and Tag 0BI0 (`lemma-power-series-over-Noetherian-normal-domain`).

## Problems and changes

The original item was statement-only. Stacks asserts the presentation, integral closure and delta calculation without proving the coefficientwise kernel or fraction identifications. Those arguments are supplied explicitly and marked agent-written. No false statement, added hypothesis, weakened conclusion or source error was found.

The existing provenance reaches a historical exceptional-fibre/ordinary-point argument below `lem-trf-local-term-locality`. I read the current chapter/unit records and the newest `literature/blueprint/latest/blueprint/sec-trace-formula/sk-i-curve-zero/` unit and ancestor proof. That newest ancestor uses contracting correspondences instead. This delivery fulfills the assigned historical algebraic input and leaves its inherited chapter, unit, source and provenance intact; it neither edits nor claims to realize the current unit as a whole.

## Searches and reuse

Before writing the split, searched the whole DAG by statement text for power series, normal domains, finite/integral algebras, quotients and Noetherianity; read the statements of every eventual dependency. `tools/blueprint_refs.py ancestor` gives `lem-trf-local-term-locality`. The full blueprint searches for `coordinate axes` and `multicross` give no matches; `normal domain` gives geometric definitions/results, not this ring calculation. A tag search for 0C1U finds this item, its ordinary-point parent, the ordinary-multiple-point and normalization-cokernel definitions, and the normalization-pair invariance lemma. None supplies this item's result independently; the parent depends on it.

Ran msearch with leanfinder, loogle, grep and leansearch for the item, and a second semantic phrasing specifically for the kernel. Exact query texts and actual results are retained in `searches.jsonl` and appended in `mathlib_searches`, along with all inherited searches. Read the candidate source: `MvPolynomial.mem_ideal_span_monomial_image` concerns finite polynomials, `MvPowerSeries.toSubring` changes the coefficient ring, substitution ideals express substitution admissibility, and Weierstrass preparation concerns a distinguished equation in one variable. None states the item's presentation/total-fraction/normalization conjunction or specializes to it in one line. Normalization monoids normalize associates, not integral closures.

Reused `lem-weil-pbc-power-series-noetherian`, `lem-weil-pbc-power-series-domain`, `lem-weil-pbc-power-series-local-ring`, and `lem-weil-pbc-power-series-normal-domain`. Only the last is outside the unit and not recorded as a Mathlib leaf; its generic tool use is declared in `split_report.tool_uses`. It does not replace any geometric route.

## Not duplicates

No new nodes. The same-tag nodes were read: the parent ordinary-point criterion uses this item, the ordinary-point definition defines a notion, the conductor-cokernel definition concerns a sheaf, and normalization-pair invariance compares two already normalized ring pairs. None duplicates or can replace the calculation here.

## Review by Q90

I checked B through E of `coord/delivery-errors.md` against the node and the local Stacks sources. There are no new statement-only nodes to test or new definition nodes to justify. Every source citation uses the actual Stacks tag and label; the item is in TeX, its statement is unchanged, and no source citation is substituted for a proof. The non-elementary results used are actual existing node statements, not facts extracted from their proofs. The twenty quotes in `citations.json` were copied from those statements. All proof steps are shorter than 2000 characters.

Step 1 uses exactly the finite coefficient product formula of `def-weil-pbc-multivariate-power-series`. Restriction to an axis is multiplicative because any decomposition of an axis exponent remains on that axis. The image computation constructs an actual preimage from the common constant and the pure positive powers. It uses neither convergence nor an unstated universal substitution theorem.

Step 2 uses the same definition to define each of the finitely many G_ij by its coefficients. Assigning each mixed exponent to its first positive pair makes each coefficient appear once. This proves membership in the algebraic ideal itself, not just its closure. The quotient convention is supplied by `def-weil-pbc-algebra-hom-quotient`, whose statement gives the quotient algebra, surjective canonical map and kernel. Both inverse maps are written. I checked that b >= 1 is needed to deduce a_0 = 0 from an axis restriction.

Step 3 uses the actual Noetherian power-series assertion in `lem-weil-pbc-power-series-noetherian` with finite b and coefficient ring k; k is Noetherian by the inverse argument written in the step. It proves quotient Noetherianity by lifting ideals and projecting generators, so there is no uncited quotient theorem. `lem-weil-pbc-power-series-domain` applies to a field and one variable and gives the coordinate domains needed for the nilpotence test. The noetherian-ring and field definition citations say exactly what those two elementary arguments require.

Step 4 takes only clause (a), unit iff unit constant, from `lem-weil-pbc-power-series-local-ring` with local base field k and d = 1. It checks that the coordinate inverses have the same constant c^{-1}, so they belong to P. It identifies the maximal ideal by units and proves the residue map is onto; no false assertion that rho(P) = k^b is made. Here ker(rho) is contained in P and is precisely the kernel of the common-constant map.

Step 5 constructs P-valued coefficients p^(i) explicitly for the spanning formula, which is exactly the finite-generation definition in `def-weil-finitely-generated-module`. It checks t_i is nonzero and uses the domain node for injectivity, rather than treating the coordinate idempotent e_i as an element of P. e_i generally is not in P. The conductor inclusion is checked by constants.

Step 6 shifts the coefficients of a nonzero denominator at its least nonzero coefficient. The only theorem needed is again the unit-constant assertion of the local-ring node. Finite b permits taking one maximum denominator exponent N. The displayed numerators prove the product localization equality, including surjectivity, without hiding a denominator-clearing theorem.

Step 7 checks both directions of the non-zero-divisor characterization, using t_i e_i in P when a coordinate vanishes and the coordinate domain node in the other direction. The conductor gives d/s^n = sd/s^{n+1}. Cross-multiplication verifies the total-fraction map is well-defined and injective; powers of s give surjectivity. Thus Q(P) is the actual localization at all non-zero-divisors, not merely a candidate ambient ring.

Step 8 constructs a monic polynomial of degree b over P for each tuple d; its ith coefficient tuple q^(i) is built by renaming the variable in d_i, so it has the same constant on every branch. Coordinate j is killed by factor j. This is an elementary calculation from the series definition and the integral-closure definition, not an application of an unrecorded finite-implies-integral theorem.

Step 9 uses exactly the concluding monic-root clause in the statement of `lem-weil-pbc-power-series-normal-domain`, after verifying the coefficient field is a Noetherian normal domain. Projection of a monic equation over P to coordinate i leaves it monic over k[[t_i]]. The node therefore proves each coordinate belongs to the required power-series ring, with fractions in its own fraction field as established in steps 6-7. Together with step 8 this proves both inclusions for the integral closure, rather than inferring it from a definition alone.

Step 10 uses the constant-coefficient part of the series definition. It supplies an explicit inverse via constant tuples for the quotient isomorphism and an explicit coordinate-difference isomorphism with k^{b-1}. The P-action is checked by rho(pd) = lambda(p) rho(d); this proves annihilation by the maximal ideal. There is no appeal to an unstated dimension formula.

I tested the full statement and arguments at b = 1: the mixed ideal and pair sum are empty, P = D = k[[t]], the denominator argument is the usual one-variable fraction calculation, the monic polynomial in step 8 is X-d, and both quotient vector spaces are zero. At b = 2 the kernel is (T_1 T_2), e_1 and e_2 are outside P, t_1 e_1 is a nonzero witness for a zero coordinate, and the quotient has basis [0,1], as required for a node. Nothing uses an algebraic closure, infinitude of k, characteristic zero or division by b; finite fields including F_2 cause no change. The step 8 polynomial also works when some coordinates coincide or are zero.

## Unfinished work

None for this one-level split. No new nodes were necessary. The independent maintainer review still applies to this direct delivery.

## Validation

Before writing this report, server `review_split` passed (ten steps, zero new nodes); server `check_dag` reported no finding introduced by the sandbox. The final delivery dry run will validate the full report and the additional quotient-definition citation.
