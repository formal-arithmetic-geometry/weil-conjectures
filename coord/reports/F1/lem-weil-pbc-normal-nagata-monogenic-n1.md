# lem-weil-pbc-normal-nagata-monogenic-n1

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-normal-nagata-monogenic-n1.json`: split Stacks Algebra 0334, Step 5, into eight explicit proof steps. The statement is unchanged.
- `dag/nodes/sec-proper-base-change/def-weil-pbc-analytically-unramified.json`: unsplit definition, Stacks 032X; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-n1-local-characterization.json`: unsplit 0333 local-to-global N-1 criterion; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-n1-descends-finite-domain-extension.json`: unsplit N-1 clause of 032K; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-nagata-localization.json`: unsplit 032U; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-analytically-unramified-n1.json`: unsplit N-1 clause of 032Y; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-analytic-unramified-principal-criterion.json`: unsplit 0330; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-local-nagata-domain-analytically-unramified.json`: unsplit 0331; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-normal-domain-fractional-principal-quotient-ass.json`: unsplit clause (3) of 031T; no Mathlib match.

The item reuses the existing 00FV/Zariski lemma, 00PQ/leading-coefficient-integrality Mathlib leaf, normal localization, finite Nagata extension and integral lying-over nodes. The generic `lem-sc-normal-dim1-dvr` statement is used as a tool at the height-one localization; its public statement is exactly the required one-dimensional normal-local-domain-to-DVR fact, Stacks 00PD. L may record this tool use at merge if the route check requires it. I did not write `tool_uses`.

## Attachments

None.

## Wanted

None. The Stacks source was read from the local read-only checkout `/tmp/stacks-project/algebra.tex`, with tags checked in `/tmp/stacks-project/tags/tags`. Mathlib searches used the available current-head sparse source at `/tmp/mathlib-f1`; the project-pinned v4.33.1 source was not available in this worktree. No new Mathlib leaf depends on that limitation.

## Source and split notes

The proof follows 0334 Step 5. Its omitted monic-polynomial detail is given by taking the residue of $x$ in $\kappa(\mathfrak m)$, choosing its monic minimal polynomial over $\kappa(\mathfrak n)$, lifting each coefficient to a fraction in $R_{\mathfrak n}$, and localizing at a common denominator outside $\mathfrak n$. The source writes `$f(X)$ in $R[x]` at line 46140; the polynomial belongs to `$R[X]` (after localization), whereas $f(x)$ lies in $S$ and in the chosen maximal ideal. The split uses this corrected notation without changing the item's statement. The case $x=0$, suppressed by the source's later assumption $x\ne0$, is handled at the start. In the finite-extension descent, the local algebra $(S\setminus\mathfrak m)^{-1}S'$ is used; localizing $S'$ at a single maximal ideal would not generally be finite over $S_{\mathfrak m}$.

Before adding nodes I searched all DAG node files by tags 0333, 032K, 032U, 032X, 032Y, 0330, 0331, 031T and by the N-1, Nagata-localization, analytically-unramified, and fractional-principal-quotient concepts. No node stated these eight facts. The existing generic DVR, Zariski and leading-coefficient facts were reused. Each new node is statement-only and self-contained; in particular analytically unramified and associated prime are defined or cited where used.

## Checks and unfinished work

`python3 tools/review_split.py lem-weil-pbc-normal-nagata-monogenic-n1` passes. `python3 tools/check_dag.py --cycles` reports zero cycles and seven unrelated pre-existing unreachable-node warnings (constructible finite pushforward / killing nodes); none of the new nodes is unreachable. No Lean code or build was attempted in Stage 1. No part of this item remains unsplit; the eight smaller new nodes are open Stage 1 items.

## Review by F1

I read Stacks Algebra 0334 Step 5, including its use of 0333, 032K, 032U, 032Y, 0330, 0331 and 031T, and checked the corresponding public node statements. The item retains precisely the normal Nagata domain, fraction-field element and N-1 conclusion of (***) in 0334. The eight new nodes state source lemmas or a needed source definition, not the monogenic conclusion: they introduce their own rings, ideals and hypotheses, cite the relevant definitions, give tag and TeX label, and contain no proof steps. I checked the worker's DAG search for those tags and concepts and found no existing duplicate. Their Mathlib searches record no exact match, so none is a claimed leaf (B1-B8, C5, D1-D2).

Step 1 applies the public 0333 local N-1 criterion after identifying S_a with R_a; Step 2 explicitly lifts the minimal-polynomial coefficients from the residue field after a common localization, filling the source's omitted detail. Steps 3-4 use the public Nagata localization, finite normalization, integral-extension and lying-over statements and the factorization of a monic polynomial into integral roots. Step 5's leading-coefficient argument is precisely the cited 00PQ statement and reduces the kernel degree by degree. Step 6 uses the public 031T quotient-associated-prime statement and the cited normal one-dimensional local DVR fact; the valuation calculation shows x belongs to R_p and then S_q=R_p. Step 7 checks each hypothesis of the public 0330 criterion using the Nagata quotient/localization and 0331 statements, then uses 032Y for N-1. Step 8 uses the finite-domain descent statement 032K and the local criterion 0333. The deductions from those cited statements are written out, with no citation to their internal proofs (C1-C4, D3-D5).

I checked x=0, a unit, repeated roots and inseparable splitting fields, and the distinction between localizing S' over S_m and localizing at a single maximal ideal. In Step 2 the polynomial belongs to the localized R[T], while its value at x lies in the maximal ideal; the source's R[x] notation for the polynomial is a typo, not a changed mathematical statement. In Step 7 the quotient is R/p because x belongs to q, so the analytically-unramified criterion is applied to the right local domain (E1-E7). The worker needed no correction. review_split passes with the cited DVR node, and check_dag finds no cycle; the seven reachability warnings are unrelated (A, F). L can inspect the cross-unit citation at merge under C8; F1 has not written tool_uses.
