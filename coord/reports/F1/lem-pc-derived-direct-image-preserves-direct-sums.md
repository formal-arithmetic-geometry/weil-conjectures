1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-derived-direct-image-preserves-direct-sums.json` — statement, split proof, and blueprint metadata.
- `dag/nodes/sec-picard-framework/lem-pc-derived-direct-image-uniform-truncation-bound.json` — statement-only prerequisite, no Mathlib match.
- `citations.json` — verbatim statement quotes for every cited node in every proof step.

2. Attachments: none. No sorry-free Lean declaration in `WeilConjectures/` carries the target blueprint tag or states this result.

3. WANTED: none. The Stacks source was available at `/home/ubuntu/c1-stacks-review/perfect.tex` and matches `literature/stacks-project/perfect.tex`.

4. Problems found: the imported item had no proof and only searches. The source proof uses a uniform truncation bound (Tag 08D5, part (2)) that was not represented by an existing DAG node, so I added `lem-pc-derived-direct-image-uniform-truncation-bound`. The existing `lem-weil-pbc-qcqs-cohomology-direct-sum` states the sheaf-level cohomology/direct-sum comparison used on the spectral-sequence $E_2$ page, and `thm-sp-truncation-e2` states the bounded-below hypercohomology spectral sequence; I cited both rather than duplicating them. I checked the target's hypotheses (qcqs morphism, quasi-coherent derived categories, arbitrary set-indexed family) against the Stacks lemma.

## Review by F1

I read Tag 08D5 and its complete proof in `perfect.tex`, including the local reduction to a quasi-compact target, the uniform bound for complexes concentrated in nonpositive degrees, the truncation triangle argument for arbitrary complexes, and the spectral-sequence reduction to quasi-coherent sheaves. I also read the full statements of `def-pc-derived-category`, `def-pc-derived-direct-image`, `thm-sp-truncation-e2`, and `lem-weil-pbc-qcqs-cohomology-direct-sum`. Step 1 uses exactly the new uniform-bound consequence and the meaning of the quasi-coherent derived subcategory. Step 2 uses the existing truncation spectral sequence and the existing qcqs cohomology/direct-sum isomorphism on each $E_2^{p,q}$ term; the uniform bound ensures finite filtration length in each total degree. Step 3 uses only the definition of the derived direct image and the elementary criterion that an isomorphism on all cohomology sheaves is an isomorphism in the derived category, after shifting to all degrees. I checked edge cases including an empty index set (both sides are zero), a singleton family (the comparison is the identity), and $f=\\mathrm{id}_X$ (the identity derived functor preserves sums). Every citation quote in `citations.json` is copied verbatim from the cited node statement. Mathlib searches were run for the item and the new prerequisite with LeanSearch (unavailable), LeanFinder, Loogle, and Mathlib source grep; no Mathlib declaration states either result.

5. Unfinished: none.

## Not duplicates

lem-pc-derived-direct-image-uniform-truncation-bound vs lem-pc-derived-direct-image-preserves-qcoh: both cite Tag 08D5, but the existing node states only that $Rf_*$ sends $D_{\\mathrm{QCoh}}(\\mathcal O_X)$ into $D_{\\mathrm{QCoh}}(\\mathcal O_Y)$, whereas the new node states the uniform high-degree vanishing bound and its truncation consequence for arbitrary objects.

## Second reading by F1

- Item statement: checked hypothesis by hypothesis against perfect.tex Tag 08DZ (perfect-lemma-quasi-coherence-pushforward-direct-sums): qcqs morphism, $D_{\\mathrm{QCoh}}$ on both sides, and arbitrary direct sums agree; corrected the source field to the tag and label.
- Step 1: checked against 08DZ's first reduction and 08D5(2), cited uniform-bound statement and derived-category definition. Wrote the truncation triangle, fixed the target name $Y$, and used the same positive $N$ for the entire family; its low-degree vanishing follows from shifting the triangle's left term. Empty and singleton families give zero and identity maps.
- Step 2: checked against 08DZ's spectral-sequence reduction, the bounded-below hypotheses and natural finite filtration of thm-sp-truncation-e2, and the exact global-cohomology statement of lem-weil-pbc-qcqs-cohomology-direct-sum. Added the affine-open restriction, higher-direct-image presheaf, and module-sheaf colimit nodes to justify passage from global cohomology to sheaves. For total degree zero only $0\\le p\\le N$ survives; $N=1$ has the ordinary two-row finite-filtration argument.
- Step 3: checked against 08DZ's shift conclusion, the definitions of derived direct image and category, and the statement of lem-pc-derived-direct-image-preserves-qcoh. Every shift gives the corresponding cohomology degree; the empty scheme and identity morphism reduce to zero and identity comparisons.
- New node lem-pc-derived-direct-image-uniform-truncation-bound: checked 08D5(2) and its truncation-triangle proof hypothesis by hypothesis. The source gives an integer bound and it may be enlarged to a positive integer; the consequence holds for each arbitrary complex in every fixed degree, with the canonical arrow from $E$ to its lower truncation. At $E=0$ both claims vanish; for a field and the identity map one may take $N=1$. It has no proof steps, is self-contained with its truncation definition cited, and is neither the item nor the existing 08D5(1) quasi-coherence node. Searches of the existing DAG by 08D5, truncation, and direct-image terms found no duplicate; the independent LeanFinder, Loogle, and Mathlib grep queries are recorded in searches.jsonl and found no matching declaration.
- Changes: corrected the 08DZ source, the truncation map's direction and quantifier, target notation, and the sheaf-level and bounded-below arguments; added three existing-node citations and their verbatim statement excerpts. The higher-direct-image-presheaf node from sk-thm-p1 and module-sheaf-colimit node from sk-thm-reduction are generic tools needed to justify the sheaf-level passage; no Picard-unit node states either fact. Kept the first review in place.
