# lem-weil-pbc-matching-object-coskeleton

## Worker report

1. Files written:
   - `dag/nodes/sec-curve-estimates/lem-weil-pbc-matching-object-coskeleton.json`: split in four proof steps.
   - `dag/nodes/sec-curve-estimates/lem-weil-pbc-coskeleton-matching-tuples.json`: one new unsplit statement node; Mathlib searches found no matching-tuple theorem.

2. Attachments: none. No sorry-free declaration or blueprint-tagged declaration for the item or helper was found in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` or `Comparator`.

3. WANTED: none. The cited Stacks source is available at `/home/ubuntu/c1-stacks-review/simplicial.tex` (the delivery node records its project-relative path).

4. The imported item had an empty proof. The earlier helper was returned because it restated the item's compatible-tuple conclusion. It has been replaced by the strictly smaller 0183 node stating only the coskeleton limit and all-truncated-simplex-family representation. The item proof now writes the 0186 reduction from all order-preserving maps to injective proper faces, citing the existing face-factorization, face-face-identity, and proper-faces nodes, then compares the two representations. No source or statement error was found.

5. Nothing remains unfinished in this split. No Lean was written or compiled, as required for stage 1.

## Review by K1

I read the pinned Stacks source `/home/ubuntu/c1-stacks-review/simplicial.tex`, Lemma 0183 (`lemma-existence-cosk`) and Lemma 0186 (`lemma-formula-limit`), including the construction of the limit over `$(\\Delta/[n])_{\\leq n-1}^{\\mathrm{op}}$`, its compatible-face tuple description, and the canonical-map identification. I also read the existing DAG statements `def-weil-pbc-simplicial-coskeleton` and `lem-weil-pbc-simplicial-matching-object` before writing.

The new helper node is strictly smaller than the item: it states only Stacks 0183's coskeleton existence, its limit-cone family indexed by all truncated simplex maps, and the canonical family $(K(\\alpha))_\\alpha$. It does not mention matching objects, matching morphisms, compatible face tuples, or the comparison isomorphism. Its three Mathlib searches (LeanSearch, Loogle, and source grep) found only generic right-Kan-extension coskeleton declarations, so it remains unsplit.

The item proof has four steps. Step 1 uses the smaller helper for the coskeleton representation. Step 2 carries out the 0186 all-map to injective proper-face reduction with the existing face-factorization and face-face-identity leaves. Step 3 uses the already reviewed proper-faces node to represent the injective families by $M_n(K)$ and identify the family of $\\mu_n$. Step 4 applies the two natural representing bijections to construct the comparison and its inverse, then identifies $\\theta c_n$ with $\\mu_n$. The `proof_deps` list is exactly the union of the cited nodes.

I checked the edge case $n=1$: the tuple condition is empty, so both representations reduce to a product of two copies of $K_0$. The JSON files parse successfully; no declaration, duplicate node, source error, or uncited non-elementary fact was found.
