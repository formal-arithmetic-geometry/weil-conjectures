# Stage 1 worker report: lem-amb-affine-space-top-trace

## Files written

- `dag/nodes/sec-smooth-purity/lem-amb-affine-space-top-trace.json` — retained the imported nine-step statement split, marked `split`; no new nodes and no Mathlib leaves.
- `citations.json` — 46 verbatim statement quotations, one for every cited node in every proof step.

## Attachments

None. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` by the exact blueprint tag, the affine-space trace names, and the relevant compact-support terminology. No declaration with this exact statement and a finished proof was found. The stage-2 declaration visible in the read-only DAG source is not an attachment in the requested source checkout and is not used as evidence here.

## WANTED

None. The proof route and its cited blueprint source are present in the repository.

## What was checked and corrected

The copied item already contained the complete imported split and its ordinary-etale finite-coefficient correction. I preserved its hypotheses, proof steps, dependency lists, blueprint ancestry, and existing tool-use metadata. I changed only the delivery bookkeeping (`status: split`, refreshed split summary/date), added the fresh required Mathlib search records, and added `citations.json`. No new node is needed: every non-elementary input is already a DAG node, and the item is not a Mathlib leaf.

The retained statement explicitly quantifies a finite commutative ring `A` annihilated by `N`, assumes `N` invertible on the Noetherian base, uses ordinary etale Tate sheaves, and states both the affine-space counit isomorphism and arbitrary Noetherian base-change compatibility. The imported statement correction records why the finite/invertible ordinary-etale setting is necessary; I did not weaken or strengthen it.

## Review by Q83

I read the item node, `sec-smooth-purity`, and unit `sk-prop-an`, together with the blueprint source `literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-an/lem-amb-affine-space-top-trace.md`. I opened the complete statement of every dependency named by all nine steps; `citations.json` copies each such statement verbatim, so each citation supplies the fact taken from it.

Step 1 checks the standard projective compactifications of the affine-line and coordinate-tower projections. It uses the projective-space properness statement, finite-type-over-Noetherian statement, the compact-support definition, the finite-type and properness definitions, and the standard-open affine-space statement. The chart calculations verify quasi-compactness, separatedness, finite type, and the Noetherian and invertibility hypotheses. Step 2 uses the open-closed distinguished triangle, triangulatedness of the right derived direct image, finiteness and exactness of the closed direct image, derived pushforward composition, and Tate pullback to identify the infinity term. Step 3 uses the normalized projective-line decomposition, the arbitrary-base Kummer sequence, and the definition of the projective trace to compute restriction and trace on both summands. Step 4 uses the derived long exact sequence and the cohomology-isomorphism criterion; the split projection is surjective in every degree, including the preceding degree, so the connecting map vanishes and the trace is an isomorphism.

Step 5 checks that this map is the actual composite adjunction counit using the open-closed adjunction, normalized projective-line adjunction, composite-adjunction formula, and Tate pullback. Step 6 verifies the shifted Tate-line case directly: extension-by-zero stalks, tensor stalks, stalk conservativity, local freeness/flatness of the Tate line, and exactness of extension by zero give the open projection comparison; the proper projection formula and the projective-line adjunction then identify the counit with `1_M` tensor the line trace. The properness and finite-type hypotheses are checked against Steps 1 and the cited definitions. Step 7 performs the coordinate-tower induction, using the affine-space identity at dimension zero, compact-support composition comparisons, the composite-adjunction formula, and Tate pullback; bounded-below inputs are checked at each intermediate stage. Step 8 proves the affine-line base-change equation by the canonical compact-support exchange, its proper and open factors, the open extension-by-zero base-change mate, projective-line counit compatibility, mate pasting, and Tate pullback. Step 9 pastes those exchange equations through the tower and uses the induction hypothesis to obtain the arbitrary-base compatibility for every dimension.

I checked the edge cases `d=0`, `e=0`, `N=1` (the coefficient ring is then zero), identity base change, and the zero-dimensional affine space. I also checked that all exchange uses are restricted to bounded-below inputs and that every cited compactification has the required separated, finite-type, proper, and quasi-compact-open hypotheses. The two proof paragraphs exceeding 2000 characters (the Tate-line projection step and the affine compactification step) were read for hidden lemmas; they contain the displayed stalk, projection-formula, naturality, and chart calculations rather than an unmentioned independent theorem. No SGA 4/4½ source was used. Fresh LeanFinder, Loogle, grep, and LeanSearch searches returned only unrelated affine-scheme, algebraic-etale, or ordinary adjunction declarations, so there is no Mathlib match.

No statement, dependency, or source error was found in this audit, and no new node or duplicate pair was introduced.
