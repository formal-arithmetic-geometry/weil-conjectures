1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-space-line-module-proj-map.json`: repaired split statement and proof; no new nodes.
- `citations.json`: updated step-3 citation to the unrestricted relative-Proj base-change node.

2. Attachments: none.

3. WANTED: none.

4. What was wrong and what was repaired:

The returned item had weakened Tag 0D2Z clause (3) by requiring an étale map and a fibre-product scheme. I restored the source's arbitrary commutative square with scheme corners, arbitrary maps `g` and `g'`, the inverse-image formula for `U(ψ)`, and the unrestricted relative-Proj comparison. The proof no longer invokes flatness or an étale-only fibre-product lemma; it cites `lemma-nagata-relative-proj-base-change-arbitrary`. Steps 1 and 2 previously asserted the algebraic-space open-locus and morphism descent. They now spell out principal opens from local generators, the overlap descent datum, the sheaf-condition construction on test schemes, and uniqueness after pulling back to the jointly surjective presentation.

## Statement corrected

The old statement is recorded verbatim in `statement_change`. The correction follows Stacks Project Tag 0D2Z, clause (3), and restores hypotheses and conclusions that the source has; it does not add hypotheses or weaken the target. Existing citers `lem-trf-scheme-ample-canonical-proj-criterion` and `lem-trf-algebraic-space-ample-local` remain valid because their uses are special cases of the restored arbitrary-base-change clause.

5. What I could not finish, and why:

Nothing remains unfinished.

## Review by NY

I reread `literature/stacks-project/spaces-divisors.tex` at Tag 0D2Z and `literature/stacks-project/constructions.tex` at Tag 01O9, including the full arbitrary base-change clause and its scheme construction. I checked the repaired statement against the source diagram: `X'` and `T'` are schemes, while `g` and `g'` are unrestricted, and `L'=(g')^*L`; the old étale and fibre-product restrictions are gone. I reread every cited node: `def-trf-algebraic-space` supplies the representable étale presentation and sheaf-valued morphisms; `def-sc-invertible-module` supplies local rank-one trivializations; `lemma-nagata-relative-proj-exists` supplies affine restrictions and their compatibility; `lem-weil-pbc-scheme-morphism-gluing` supplies uniqueness on scheme-chart overlaps; `def-pc-module-pullback` supplies the pullback formula; and `lemma-nagata-relative-proj-base-change-arbitrary` states exactly the unrestricted Proj comparison used in Step 3. Step 1 now checks surjectivity locally by principal opens and explains why those opens descend on the presentation overlaps. Step 2 explicitly glues local maps by the target algebraic space's sheaf condition on an étale cover of every test scheme, then checks functoriality and uniqueness. Step 3 uses only pullback-locality and the arbitrary Proj comparison, so no flatness or étaleness is assumed. Step 4 still identifies the scheme specialization with the ordinary invertible-module construction. I tested identity and empty generation loci, zero positive-degree algebra, a trivial line module, and arbitrary non-flat affine base change; the formulas give the expected empty/whole opens and the usual affine Proj map. The citation quotes were checked verbatim, and `proof_deps` is the union of the step uses.
