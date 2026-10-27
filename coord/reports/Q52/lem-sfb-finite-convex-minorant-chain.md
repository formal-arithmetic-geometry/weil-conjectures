## Worker report

Files written: `dag/nodes/sec-six-functors-basics/lem-sfb-finite-convex-minorant-chain.json` (statement, now split; no Mathlib match), `citations.json` (empty list: all five proof steps are elementary), and this report. `searches.jsonl` is the unmodified msearch log.

## New nodes

None. Zero new nodes and zero Mathlib leaves. The selection of a least slope is proved by a finite scan; its existence is not left as a convex-hull or minimization theorem. The weighted-secant identity is field arithmetic, so neither deserves a new node.

## Attachments

None. Searched the whole project `lean/WeilConjectures/` by the item id and by convex, minorant, secant and lower-hull notions; no matching declaration was found. Also checked `lean/Sheaf/` for the item id, convexMinorant, convex_minorant and secant.

## Literature

WANTED: Ian Morrison, *GIT Constructions of Moduli Spaces of Stable Curves and Maps*, arXiv:0810.2340, Section 2.4, Lemma 6 and Figure 2, printed pp.11–12, for lem-sfb-finite-convex-minorant-chain. The named local PDF is absent. Read the primary source online at https://arxiv.org/pdf/0810.2340, especially printed p.11, proof of Lemma 6: the polygon through an endpoint-containing subsequence and its lower convex envelope. The source takes the finite envelope construction for granted. The five-step minimum-secant construction fills that omission; proof_origin.by is agent. No SGA source is used. No Stacks tag is assigned: this is finite ordered-field arithmetic, not a Stacks theorem.

Read the latest blueprint at `literature/blueprint/latest/`, snapshot main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345, including the ctf-stability unit and the direct-images proof paragraph (3). The existing item's long from.place locates the stable-curve/projectivity prerequisite below that paragraph. The chapter and unit route is unchanged.

## Existing-node and Mathlib searches

Whole-DAG keyword searches for convex minorant, lower convex, minimum slope and finite minimum found the item and its parent among irrelevant algebraic dimension/minimum results. Read `lem-sfb-strict-codegree-polygon-gap`: it applies this item to weights with n=N-1 and uses precisely contact, minorization and nondecreasing differences; it is a consumer, not a replacement. Blueprint searches `convex minorant`, `lower convex` and `secant` each returned zero. `blueprint_refs.py ancestor lem-sfb-finite-convex-minorant-chain` returned None: the existing created.item ancestry ends at a Lean module name through lem-sfb-admissible-direct-image. Preserve inherited from.node=null and via; the exact inherited from.place already records the intended blueprint passage.

Ran msearch with this item and Q52 for LeanFinder, Loogle, grep and LeanSearch, and a second LeanFinder phrasing about selecting minimum secant slopes. All returned successfully and the exact queries/results are recorded from searches.jsonl. Kept all earlier Q13 searches without claiming to have rerun them. Read the relevant local Mathlib sources: Analysis/Convex/Piecewise.lean:42 (joining already convex functions under monotonicity assumptions); Analysis/Convex/Slope.lean:133 and :172–198 (criteria or inequalities assuming an already convex function); Analysis/Convex/StdSimplex.lean:160 and Analysis/Convex/Combination.lean:342 (convex-hull descriptions); Analysis/Convex/Approximation.lean:70–110 (affine minorants of an already convex lower-semicontinuous function). These supply no contact subsequence for arbitrary data in a one-line specialization. The second LeanFinder's map_le_lineMap_iff_slope_le_slope is another interpolation/slope equivalence, not the required existence theorem.

## Not duplicates

No new-node pairs. Nothing newly created shares a tag with an existing node.

## Errors and unfinished work

The item was unsplit and mathematically correct. No statement correction, extra hypothesis, normalization or target change was needed. Its finite formulation deliberately avoids the parent's already-recorded factor-two problem in the displayed Morrison estimate. No incomplete proof step remains in this item. No Lean file or compiler/build tool was used.

## Review by Q52

I read Morrison's lower-envelope paragraph and Figure 2 and compared every conclusion of the item against the proposed construction. The supplied elementary proof constructs an endpoint-containing chain, not an unrelated arbitrary affine lower bound. It does not claim the stronger maximal-minorant property, which the item does not request.

Step 1 has no cited statements: its finite scan starts in a nonempty set because p<n, and its explicit induction invariant proves minimality. The denominator q-p is positive. Retaining any tied minimizer is legitimate; no strict minimum or uniqueness is assumed.

Step 2 has no cited statements: the recursion uses that minimum and increases bounded integer indices. The written bound a_j>=j forces a stopping value n within n steps. Since n>=1, the first vertex is not already the last and h>=1. This is elementary finite induction, not a compactness assertion.

Step 3 has no cited statements: expanding w_p+(i-p)s(p,q) gives the exact numerator and denominator of the item. Both endpoint evaluations are checked, so shared-endpoint well-definedness follows. At an interior integer i, minimality can be applied because p<i<=q<=n; multiplying by the positive i-p preserves the inequality. I checked the direction is v_i<=w_i. Thus the contact and minorant clauses follow from the actual formulas.

Step 4 has no cited statements: I expanded the weighted identity using the definition of s. Applying minimality at p to the later vertex r gives the needed first inequality; subtracting (q-p)s(p,q) and dividing by r-q>0 proves the correct nondecreasing orientation. This is one field rearrangement, not an invocation of a theorem about convex hulls.

Step 5 has no cited statements: the half-open segments partition the integer edge indices 0,...,n-1. Each unit increment has exactly its segment slope, including the edge ending at a shared vertex. Their segment indices are ordered, so Step 4 proves the displayed adjacent-difference inequality. For n=1 there are no adjacent slope comparisons. Every step is under 600 characters; no long step conceals a general lemma. I read def-weil-field's statement (commutative ring with inverses for nonzero elements), retained it as the statement dependency, and introduced no new specialized notions requiring definition nodes. citations.json is empty because uses is empty in all proof steps, rather than because a citation was omitted.

I checked small cases: n=1; a constant sequence with all slopes tied; an affine decreasing sequence; the three-point data (0,-1,-3), whose chord is below the middle point; and (0,-2,-3), where the interior vertex must be selected. Negative weights and a nonzero terminal weight cause no problem. As a sanity check, a Python computation with exact rational arithmetic tested all 19,525 sequences with n=1,...,5 and entries in {-2,-1,0,1,2}, including every decreasing sequence in that grid; every endpoint equality, minorant inequality, shared-endpoint agreement and discrete convexity inequality passed. This finite check supplements the written proof.

Checked delivery-errors B–E against the actual node: no new unsplit statement or duplicated clause; single TeX escapes; no hypothesis silently added; no derived-object comparison, hidden convex-envelope theorem, circular dependence or off-unit proof citation. No source sentence is used as an uncited black box. No proof correction was required after this reading. The remote check_dag invocation completed successfully: no finding introduced by the sandbox or on its nodes. The first attempted srvcheck path mistakenly included batch2 and did not execute; rerunning the exact instructed path succeeded. Final dry-run and delivery outputs are recorded separately in the delivery log.
