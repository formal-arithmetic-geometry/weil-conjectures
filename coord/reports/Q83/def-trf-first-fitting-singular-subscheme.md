1. Files written:
- `dag/nodes/sec-trace-formula/def-trf-first-fitting-singular-subscheme.json`: definition, split; no new Mathlib leaf.
- `citations.json`: empty, because the item is a definition and has no proof steps.

2. Attachments: none. No sorry-free declaration in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` states this item (searched by item id, Fitting/singular keywords, and likely declaration names).

3. WANTED: none.

4. The imported definition was already mathematically the right construction. I retained its statement and dependency list, marked it `split`, and recorded the exact Mathlib search results and blueprint provenance. No proof node was created: a theorem asserting generator-independence/localization/gluing here would restate clauses of this definition, while the cited Stacks results are the source for those properties. The source field points to `literature/stacks-project/divisors.tex` and the relevant More on Algebra source, with tags 0C3I, 0C3J, 0C3K, 07Z6, 07Z8, and 07ZA.

5. Nothing remains unfinished.

## Review by Q83

I read the item and its three statement dependencies: `def-sc-relative-differential-sheaf`, `def-weil-closed-immersion`, and `def-weil-finite-type-morphism`. The affine construction is checked against Divisors Section `section-fitting-ideals` and its `lemma-base-change-and-fitting-ideal-omega`: a locally finite type affine chart has a finite type algebra and finite type relative differentials; the displayed kernel presentation gives the first Fitting ideal, and base change/localization identifies the local ideals so they glue. I read More on Algebra Section `more-algebra-section-fitting-ideals`, `lemma-fitting-ideal` (Tag 07Z8), and `lemma-fitting-ideal-basics` (Tag 07ZA), including the convention that 0-minors generate the unit ideal, so the stated `n≤1` convention is correct. I also checked the singular-locus discussion and Tags 0C3I–0C3K, which supply formation under base change, the zero-Fitting unramified locus, and the smooth-locus identification used by the downstream nodal-family lemma. The exact statement introduces all objects it uses and does not assume finite presentation where only locally finite type is required. Whole-DAG and whole-blueprint searches found no duplicate Fitting-ideal or singular-subsheme node, and the Mathlib searches found no Fitting-ideal declaration. Since this node has no proof steps, `citations.json` is intentionally empty.
