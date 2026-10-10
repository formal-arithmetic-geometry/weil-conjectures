# Stage 1 report

1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-weil-pbc-closed-immersion-products.json` — statement split, no new non-Mathlib proof leaves.
   - `dag/nodes/sec-curve-estimates/lem-weil-pbc-qc-open-immersion-finite-type.json` — statement, Mathlib verdict: match.
   - `citations.json` — verbatim citations for every proof-step dependency.
2. Attachments: none. No declaration tagged `(blueprint: lem-weil-pbc-closed-immersion-products)` was found in the slopmaster2 source, and no sorry-free declaration states this item.
3. WANTED: none.
4. What was wrong: the imported final sentence claimed that every open immersion is of finite type. This is false without quasi-compactness: for an affine scheme with infinitely many basic opens, their non-quasi-compact union is an open subscheme whose inclusion is not quasi-compact and hence not finite type. I corrected the item to the quasi-compact open-immersion statement used by the surrounding blueprint. The composite and base-change facts already existed as `lem-weil-pbc-closed-immersion-comp` and `lem-weil-pbc-closed-immersion-base-change`, so I created no duplicate nodes.
5. Nothing remains unfinished.

## Review by C1

I read the imported item node, its `sk-thm-br` unit record, the chapter record, and the source proof text represented in the node. I also opened the existing composition and base-change nodes and checked their complete statements: the first exactly supplies composition of two closed immersions, and the second exactly supplies the relevant pullback projection. For step 1 I cite only the composition statement. For step 2 I cite only the base-change statement and instantiate it twice, once for each factor. Step 3 cites those same two statements and performs the explicit composite. Step 4 cites the new node, whose statement exactly supplies finite type for a quasi-compact open immersion.

For the new node I searched the DAG and blueprint for an existing statement and found none. I checked Mathlib source at `Immersion.lean:190`, `FiniteType.lean:43`, and `QuasiCompact.lean:43`; LeanSearch, Loogle, and source grep all support the one-line specialization recorded in `mathlib_match`. I tested the corrected hypothesis on the empty open and on a principal open (both quasi-compact), and tested the removed unqualified claim on an infinite union of principal opens in an affine scheme, where quasi-compactness fails. The item and new node carry blueprint references, and `citations.json` quotes the cited node statements verbatim.
