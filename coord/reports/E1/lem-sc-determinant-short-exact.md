# Delivery report

1. Files written:
   - `dag/nodes/sec-picard-framework/lem-sc-determinant-short-exact.json` (item, statement split).
   - `dag/nodes/sec-picard-framework/lem-sc-local-splitting-finite-free.json` (new unsplit statement; no Mathlib match).
   - `dag/nodes/sec-picard-framework/lem-sc-exterior-top-direct-sum.json` (new unsplit statement; no Mathlib match).
2. Attachments: none.
3. WANTED: none; the imported blueprint source was available, and the proof is marked agent-authored because it supplies the omitted gluing details.
4. The item had no Lean declaration and no existing DAG node stated either supporting fact. Mathlib search found only module-level exterior-power infrastructure and no sheaf determinant theorem. The item statement was retained, with its blueprint place made precise.
5. Nothing remains unfinished in the split; the two supporting facts are intentionally unsplit queue nodes.

## Review by E1

I read the item source `literature/blueprint/master/blueprint/sec-picard-framework/sk-thm-picard-rr/lem-sc-riemann-roch.md`, specifically the determinant paragraph in the proof of (*), and checked the item statement against it: a short exact sequence of finite locally free modules has locally split form, and the determinant is the top exterior power. I searched the whole DAG and the slopmaster2 Lean sources for the item tag, determinant, exterior power, and short-exact terminology; no exact declaration or existing node was found. The Lean search, Loogle, and Mathlib-source searches recorded in each new node were also performed; they found no matching sheaf theorem.

For step 1, the local-splitting node now states constant-rank local freeness using `[def-amb-finite-locally-free-module]`; I checked that the cover is refined so both end terms are free on each chart, which supplies the bases needed later and gives `r₂=r₁+r₃` on the split chart. For the direct-sum node, I checked that `[def-weil-pbc-free-module]`, `[def-weil-pbc-exterior-algebra]`, and `[def-weil-pbc-module-tensor-product]` define exactly the free modules, exterior powers, and tensor product named in its statement; the former flat-sheaf citation was removed.

For step 2 of the item, `[lem-sc-exterior-top-direct-sum]` gives the canonical top-degree module isomorphism, while `[lem-weil-pbc-exterior-power-free-basis]` states that the wedges of a free basis form the exterior-power basis, including the rank-zero and vanishing cases. I checked the sheaf application chartwise and its compatibility with restriction. For step 3, I replaced the nonexistent global inclusion by the actual local formula using a splitting `s`. If `s'` is another splitting, `s'(b)-s(b)` lies in the image of `u`; after expansion every changed term has `r₁+1` factors in the free rank-`r₁` module, so the cited exterior-power basis lemma makes it zero. This proves overlap agreement, restriction compatibility, gluing, and the zero-rank convention.

I tested the supporting statements on ranks `(0,0)`, `(1,0)`, `(0,1)`, and `(1,1)`: the direct-sum wedge map is respectively the identity on `O`, the evident identification, and the usual two-vector determinant map. No hypotheses beyond constant finite local freeness and exactness are used. The repair corrected all four returned issues: invalid flatness citations, unicode proof text, missing free trivializations, and the nonexistent global inclusion; no statement was weakened.
