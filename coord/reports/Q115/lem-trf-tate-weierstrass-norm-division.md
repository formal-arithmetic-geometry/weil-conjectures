# Q115: lem-trf-tate-weierstrass-norm-division

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-tate-weierstrass-norm-division.json`: statement, now split; the statement and its hypotheses are unchanged. The proof has seven steps. Existing metadata and the earlier Q67 searches are retained, with fresh searches appended.
- `dag/nodes/sec-trace-formula/lem-trf-restricted-series-gauss-completion.json`: one new statement-only, unsplit analytic prerequisite; no Mathlib match. It asserts the complete Gauss-norm restricted-series algebra, truncation density and isometric regrouping of one variable. It asserts no division or preparation conclusion.
- `citations.json`: one entry for every step/node citation, quoting the actual statement verbatim.
- `searches.jsonl`: the unmodified search-command log. `write_split.py` is only a sandbox drafting aid and is not part of the DAG delivery.

## Attachments

None. Searches by the exact item tag, Weierstrass, Tate algebra and Gauss norm in the read-only project sources found no analytic declaration for the item, nor a declaration stating the new prerequisite. The unrelated normalized arithmetic Gauss lemmas do not qualify. Neither upstream master nor slopmaster2 supplies an attachment. No Lean was written and nothing was compiled.

## Wanted sources

WANTED: Bosch–Guntzer–Remmert, *Non-Archimedean Analysis*, the Weierstrass division and preparation theorem for strictly convergent series with Gauss-norm bounds, for lem-trf-tate-weierstrass-norm-division.

WANTED: the same book, basic Gauss-norm completeness, truncation density and variable regrouping of strictly convergent series, for lem-trf-restricted-series-gauss-completion.

The item already named `literature/bosch-guntzer-remmert-non-archimedean-analysis.pdf`, but that book is absent from this checkout and from the obtained-literature list. I did not download it or claim to have read it. All proof steps and proof_origin explicitly identify an agent reconstruction. No unverified theorem/page number, Stacks tag or SGA reference has been introduced. These analytic results are not being attributed to an unrelated algebraic Stacks lemma.

## Issues found and changes made

The original item was an unsplit analytic theorem with a descriptive, unavailable BGR source. Its statement is valid; no STATEMENT-DISPUTED change was needed. The elementary polynomial part, the completion argument, the correction sequence and the preparation step now carry the argument rather than each becoming a node restating a clause.

The chapter/unit records and ancestor `lem-trf-local-term-locality` were read. This is a historical analytic prerequisite below the former completed-local-ring comparison, as its existing blueprint metadata says; it is not a replacement route for the current contracting-correspondence theorem. No chapter or unit was changed, and the item is not the key node of its unit. The child's blueprint ancestry inserts this item in `via`, keeps the exact nearest ancestor, and explains which historical analytic invocation it serves.

Mathlib's `MvPowerSeries.IsRestricted.subring` (Restricted.lean:107) gives the restricted subring, and GaussNorm.lean defines its norm expression and supplies individual inequalities. I read Restricted.lean, the GaussNorm definition, and PiTopology.lean:154–158, 369–382. The `WithPiTopology` density and completeness hits concern coefficientwise product uniformity on *all* formal series, not the Gauss-norm topology. I also read the introduction and divisor conditions of PowerSeries/WeierstrassPreparation.lean:15–110: its adic coefficient-ring theorem does not supply analytic convergence and bounds. Thus neither the item nor its new child is a one-line Mathlib specialization. Both semantic phrasings for each search question were run and their hits inspected; all recorded new queries are in the command's log.

## Not duplicates

lem-trf-restricted-series-gauss-completion vs def-trf-restricted-series-presentation: the latter defines the restricted subring and predicates for presentations and quotient norms; its statement asserts neither completeness of the Gauss-norm series ring nor the isometric regrouping theorem.

lem-trf-restricted-series-gauss-completion vs lem-trf-affinoid-polynomial-closed-point-comparison: that parent's statement concerns Noetherian affinoid quotients and completed local rings at maximal ideals; it does not state the isometric regrouping theorem, and its proof depends on this item, so citing it here would be circular. The new child isolates the elementary analytic infrastructure needed before division, rather than duplicating that parent theorem.

lem-trf-restricted-series-gauss-completion vs lem-wf-nonarchimedean-series-substitution: that theorem concerns univariate scalar series, pointwise evaluation and formal composition at a specified radius. It asserts no Gauss-norm completion of multivariate coefficient families or iterated-series identification.

lem-trf-restricted-series-gauss-completion vs lem-trf-tate-weierstrass-norm-division: the child states algebraic norm properties, completeness, density and regrouping, with no distinguished divisor, quotient, remainder or prepared polynomial. It is strictly prior infrastructure, not a division/preparation clause moved into another node.

Whole-DAG searches by Gauss norm, restricted series, Tate algebra, Banach algebra, completeness and density found no theorem giving this child. `blueprint_refs.py search` returned no blueprint match for Weierstrass, Gauss, restricted series or Banach. The whole-DAG/source id search found no pre-existing child id. No same-tag pair exists because the child cites no Stacks tag.

## Review by Q115

I read delivery-errors B through E in full, the stage-1 brief and stage document, SETUP's three levels, GOAL and dag-sync. For the item and its one new node the proposed BGR source is unavailable; the report and proof metadata say so, and the mathematical argument is supplied rather than pretending to quote that book. For citations I reopened the polynomial definition and the restricted-series presentation definition and read their statements. I checked the child's statement against every use in the item's steps. The supplied quotes are the literal cited statements.

Step 1 uses the child's stated completeness, ultrametric/product inequalities and isometric regrouping, and the polynomial definition's finitely supported coefficient convention. Completeness of E is simply the coordinatewise completeness of finitely many copies of A. The small-tail constant really is the norm of e, and p has norm one because its degree-d coefficient is 1.

Step 2 is a finite degree induction, written explicitly from the polynomial definition and step 1's estimates. Subtracting the leading monomial times p lowers degree and never increases norm. Monicity, not a domain assumption, proves the degree identity needed for uniqueness. This is an elementary step and not a new lemma. For d=0, p=1 and the zero remainder are given explicitly.

Step 3 uses the child's *Gauss-norm* completeness and regrouping, not coefficientwise product-topology completeness. The difference estimate makes the polynomial quotients and remainders Cauchy, bounds their limits and makes the extension independent of the chosen approximants. Both inverse identities are checked on polynomial approximants pv^(N)+t. This prevents a hidden assumption that arbitrary series already admit division.

Step 4 uses the child's strong triangle inequality and completeness. I checked the sign in h_(j+1)=-e v_j: h_j=g v_j+t_j+h_(j+1), so the finite telescoping identity is exact. Bounds are c^j times the original norm; tail sums tend to zero without an archimedean factor 1/(1-c). Limits of the remainders stay in the same finite coefficient space E. Continuity of fixed multiplication is proved by the product inequality. No general fixed-point, geometric-series or bounded-map extension theorem is silently used.

Step 5 is the elementary real inequality ||v|| <= c||v|| with c<1 after applying the already constructed Q_0. It proves uniqueness even for decompositions without any assumed bound; the conclusion is not just uniqueness of the iteration's output.

Step 6 first uses division already proved, then the child's completeness for explicit geometric partial sums. Q_0(X^d)=1 implies ||1-b||<=c, which is the necessary extra estimate for inverting b. The finite two-sided inverse identities and their limits are written down. Thus g=b^(-1)(X^d-r_*) has the required monic factor and both unit bounds. I corrected the draft's ambiguous paired-norm notation to state the two bounds separately.

Step 7 checks d=0, s=0, h=0 and e=0. The degree convention for the zero remainder is its empty support (degree minus infinity), not a natural-number degree erroneously required to be less than zero. For the new child, n=0 gives F, the zero series has norm zero, and regrouping works in both directions: finitely many exceptional coefficient pairs imply coefficient norms tend to zero in X; conversely, only finitely many X-coefficients exceed a fixed threshold, and each has only finitely many exceptional Y-coefficients. A Gauss-Cauchy family's coefficientwise limits are uniformly approximated by any sufficiently late member, so remain restricted. This tests the key claims of the new unsplit node without adding a proof to it.

B: the new statement introduces its objects, cites the actual restricted-series definition and field definition, has an exact ancestor/via reference, and has no proof or proof dependencies. Search results are genuine, with no false Mathlib leaf. C: every external non-elementary input is the new completion/regrouping node; every other inference is written or relies on an earlier established step, not on an uncited source theorem. D: division, uniqueness and preparation remain in this item's proof and are not relabelled children. E: completeness, the uniform upper-tail bound <1 and monicity are precisely the hypotheses used, with no discretely valued, spherically complete, local-coefficient-ring or positive-degree assumption. There are no proof steps over 2000 characters and no undeclared off-unit tool use.

## Unfinished work

No part of this item's argument remains unfinished. The new statement-only prerequisite is intentionally left unsplit as the one-level stage-1 contract requires. The BGR reference remains WANTED. Required server dry run and delivery results are reported by the delivery command.
