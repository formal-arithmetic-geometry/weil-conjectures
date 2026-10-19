1. Files written: `dag/nodes/sec-trace-formula/lem-trf-injective-target-hom-symbol.json` (item, split; no new nodes); `citations.json` (step citations).

2. Attachments: none. No sorry-free declaration in `WeilConjectures/` states this item exactly.

3. WANTED: none.

4. What was wrong or incomplete: the imported item had an empty proof and no split report. I retained its statement and dependencies. Its source (Stacks Tag 05TP) gives the compatible split-filtration description, while the exact symbol sequence is an extracted consequence; the report records that provenance. No statement error or duplicate node was found. The existing node `lem-trf-injective-graded-filtration-splits` supplies the needed target decomposition, so no new node was created. The Mathlib searches found only unrelated filtered-index, graded-object, and ordinary injective-resolution declarations.

5. What could not be finished: nothing.

## Review by Q143

I read the target node, the existing split-filtration node `lem-trf-injective-graded-filtration-splits`, and the three definition nodes `def-sp-abelian`, `def-sp-filtration`, and `def-sp-injective-resolutions`. Step 1 uses exactly the split node's assertion that an object with finite filtration and injective graded pieces is isomorphic to a finite direct sum whose tails are the filtration; the quotient inclusion `gr^p X → X/F^{p+1}X` follows from the induced and quotient filtration definitions in the abelian category. The injective definition says restriction along this monomorphism is surjective, giving each component extension.

Step 2 uses the same tail identification and finite biproducts from the abelian-category definition. I checked the filtration inequality componentwise: indices below the source step vanish, and indices at least that step land in the target tail shifted by `r`; the `p` component is the only one surviving in degree `p+r`. Step 3 uses the kernel characterization of the quotient defining `gr^{p+r}Y` and verifies both inclusions between the kernel of `σ_r` and `G^{r+1}`. Step 4 checks precomposition and postcomposition by writing the induced maps on each quotient; the filtration-preserving condition is exactly the one in `def-sp-filtration`, and injectivity of the postcomposition target allows the same exactness argument there. I tested the one-step filtration, zero objects, and indices outside both finite intervals. All cited statements say the facts used, every step has a literature place, and no long step hides a separate lemma.
