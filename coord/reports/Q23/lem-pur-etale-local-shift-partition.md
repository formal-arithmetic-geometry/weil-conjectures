# Stage 1 report

1. Files written:

- `dag/nodes/sec-smooth-purity/lem-pur-etale-local-shift-partition.json` — statement split, with three proof steps.
- No new node files; the existing Mathlib node `lem-weil-pbc-etale-morphism-open-map` supplies the open-image fact.
- `citations.json` — verbatim step citations.

2. Attachments: none.

3. WANTED: none.

4. I found no finished declaration tagged `lem-pur-etale-local-shift-partition` in the project source. I read the item, its unit `sk-prop-a1-inv`, chapter `sec-smooth-purity`, and the main-20261015 affine-line proof. The imported item is the proof's extracted Step 1. I retained its hypotheses and made the hidden stalk argument explicit. The existing node `lem-pur-proetale-inverse-image-stalk` supplies the inverse-image stalk comparison, and the existing Mathlib leaf `lem-weil-pbc-etale-morphism-open-map` supplies openness of étale images. I searched the whole DAG and blueprint for shift-locus, clopen shift, and cohomology-degree statements; no duplicate or more general project node states this result.

## Review by Q23

For Step 1 I checked the exactness statement of `prop-weil-pbc-proetale-constant-exact`, the cohomology definitions in `def-weil-derived-cohomology-sheaves` and `def-weil-abstract-derived-category`, the local-constant definition, and the geometric-stalk comparison in `lem-pur-proetale-inverse-image-stalk`. These statements justify commuting cohomology with pullback and comparing the stalk of the pulled-back complex with the stalk downstairs. Since the local model has stalk $A$ and $A$ is nonzero, the unique nonzero degree is exactly the displayed shift; applying this at two lifts of a point in an image intersection proves equality of shifts.

For Step 2 I read the existing Mathlib leaf `lem-weil-pbc-etale-morphism-open-map` and its Mathlib source at `UniversallyOpen.lean` lines 48 and 147 and `Etale.lean` lines 108 and 112. Étale gives flatness and local finite presentation through the smooth relative-dimension-zero instances; `UniversallyOpen.of_flat` then gives `UniversallyOpen`, and `Scheme.Hom.isOpenMap` gives openness. Thus the unions defining $Y_n$ are open, and pairwise disjointness plus exhaustiveness makes each complement open as well.

For Step 3 I checked that boundedly many nonzero cohomology sheaves give a finite set of possible degrees. A nonempty $Y_n$ has a nonempty covering member with a geometric point, and Step 1 gives a nonzero stalk of $\mathcal H^{-n}(K)$, so only finitely many $n$ occur. The inclusion of every nonempty covering image in its indexed $Y_{n_\alpha}$ is immediate from the definition; empty members may be removed. I tested the edge cases of a one-point base, a disconnected base with different shifts on clopen components, an empty covering member, and the zero/nonzero coefficient distinction. No statement was changed and no SGA source was used.

5. I could not identify any remaining unfinished part of this split.
