1. Files written:

- dag/nodes/sec-deligne-laumon-a1/lem-per-affine-open-strict-local-cd.json — item, statement split, no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-affine-open-strict-local-cd-constructible.json — statement-only child, no Mathlib match.
- citations.json — verbatim citations for every proof-step use.

2. Attachments: none.

3. WANTED: none.

4. What was wrong or incomplete in the imported item: the item had no proof, although its source explicitly supplies the constructible affine-open bound (ILO XV Corollary 1.2.4). The missing part was the extension from constructible sheaves to arbitrary finite-ring module sheaves; this is supplied using the existing filtered-colimit and cohomology-continuity nodes. The source and statement use the ordinary small étale site and underlying abelian cohomology throughout; no coefficient-category identification was added beyond the existing module-to-abelian comparison.

## Not duplicates

lem-per-affine-open-strict-local-cd-constructible vs lem-per-artin-gabber-affine-curve: the new node concerns ordinary finite prime-power torsion sheaves on affine opens of excellent strictly henselian local schemes, while the existing node concerns perverse derived pushforward for affine finite-type morphisms between separated finite-type schemes over a field.

lem-per-affine-open-strict-local-cd-constructible vs lem-per-strict-local-etale-dimension-bounds: the new node is the affine-open constructible cohomological-dimension bound q>d; the existing node concerns punctured strict-local schemes, support-dimension bounds q≥2e, supported cohomology, and generic-point continuity.

5. What I could not finish, and why: nothing. No Lean files were written and no compiler or Lake tool was run, per the stage-1 restrictions.

## Review by NA

I read the item node, its parent lem-per-artin-gabber-affine-curve, the unit sk-p-dl-a1-perverse, the chapter record, the current main blueprint proof, and ILO Expose XV Corollaries 1.2.2 and 1.2.4 (printed pp. 219–220). I also read the existing statements of lem-weil-pbc-module-sheaf-colimit-constructible, lem-weil-pbc-affine-scheme-qcqs, lem-weil-pbc-cohomology-filtered-colimit, and lem-weil-pbc-etale-module-cohomology-forget, plus the new constructible child. The child matches ILO's constructible affine-open assertion with the same prime-power coefficients, excellent strictly henselian local hypotheses, affine open, and bound q>d. The item retains the arbitrary sheaf statement and its exact hypotheses.

Step 1 cites only the child, whose statement explicitly supplies the vanishing for every constructible C and q>d; its non-elementary input is exactly ILO XV Corollary 1.2.4. Step 2 cites the filtered-colimit statement, which explicitly gives a small filtered diagram of constructible Λ-module sheaves and a colimit cocone, and cites the affine-qcqs statement, which explicitly supplies quasi-compactness and quasi-separatedness of V. Step 3 cites the filtered-cohomology statement, whose displayed isomorphism is exactly the required passage through H^q, and the module-to-abelian statement, whose natural isomorphism identifies module cohomology with underlying abelian-sheaf cohomology. Step 4 uses the child for each constructible term, then the same two comparison statements to conclude that the filtered colimit is zero. The only elementary inference is that a filtered colimit of zero groups is zero and that the displayed isomorphism transfers this vanishing.

I checked the edge cases d=0, V=empty, and M=0: the stated conclusion is vacuous or immediate in each case, and no proof step assumes d>0, nonempty V, or constructibility of M. The Mathlib searches were run with LeanFinder, LeanSearch, Loogle, and Mathlib grep; they found only general affine/site/Krull-dimension ingredients and no étale cohomological-dimension theorem. The new child is therefore an unsplit non-Mathlib statement node. No attachment or source correction was needed.
