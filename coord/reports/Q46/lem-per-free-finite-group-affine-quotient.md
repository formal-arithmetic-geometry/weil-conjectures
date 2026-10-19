1. Files written:

- `dag/nodes/sec-deligne-laumon-a1/lem-per-free-finite-group-affine-quotient.json`: existing statement split into nine proof steps; no new nodes.
- `citations.json`: one verbatim statement quote for every cited node in every step.

2. Attachments: none.

3. WANTED: none.

4. The item statement agrees with Stacks Spaces Properties Tag 07S7 (label `lemma-quotient-scheme`) in the affine case, with the finite locally free relation calculation supplied by the existing DAG node `lem-a1-finite-flat-affine-relation-quotient` (Stacks Groupoids Tag 03BM). I retained the stronger explicit statement's base-change and categorical clauses and proved them from the represented fppf orbit sheaf. I did not create a duplicate of Tag 03BM or move the item's conclusion into a new node. The local chart argument checks the constant finite group action maps directly; it does not assume connectedness, etaleness, Noetherian hypotheses, or an affine base.

5. Nothing remains unfinished in this stage.

## Not duplicates

No new nodes were created, so there are no new-node duplicate pairs.

## Review by Q46

I read the item record, the chapter and unit records, the Stacks proof of `lemma-quotient-scheme` in `literature/stacks-project/spaces-properties.tex`, the affine relation proof `proposition-finite-flat-equivalence` in `literature/stacks-project/groupoids.tex`, and the fpqc descent and scheme-gluing arguments in `descent.tex` and `schemes.tex`. I also checked the existing DAG statements before citing them. The affine chart step uses the existing finite-flat affine relation quotient exactly for an affine $X_i$ over an affine base $U_i$; its statement supplies the invariant spectrum, finite locally free surjection, fppf orbit sheaf, and kernel-pair isomorphism. The open-subfunctor step uses the existing scheme representability criterion and verifies representability of each inclusion by the open $T\times_SU_i$; the hypotheses do not require pairwise affine intersections. The finite locally free conclusion is checked on the same open cover with the existing finite-local-on-target statement and the definitions of flatness and local finite presentation. For base change I checked that fppf coverings and finite morphisms are stable under base change, then base-changed the kernel-pair comparison. For categoricality I checked local lifting along $T\times_{Q'}X'\to T$ and equality of representatives via the kernel-pair isomorphism. I tested the edge cases in the prose: the empty scheme and trivial group are covered by the affine quotient node and gluing criterion, and disconnected test schemes are handled by locally constant group elements and clopen decomposition. I ran the required LeanSearch, LeanFinder, Loogle, and Mathlib grep searches with `msearch.py`; their hits concern set-action quotients, abstract Galois categories, or generic affine properties and do not state this scheme quotient theorem. The item statement and all imported metadata were retained; only its proof, proof dependencies, proof origin, status, mathlib search records, and split report were filled.


Step-by-step citation audit:

1. `lem-weil-pbc-flat-lfp-open` supplies openness of fppf maps. The explicit finite affine refinement verifies `def-weil-pbc-fpqc-covering`; `lem-weil-pbc-fpqc-representable-descent` therefore applies to arbitrary target schemes. `def-weil-pbc-sheafification` supplies the universal property, and `lem-cbc-set-presheaf-sheafification-local-bijection` applies to the unit because its sheafification is an isomorphism. No effective-epimorphism claim is taken from a definition.
2. `pqf-def-affine-morphism` makes each $X_i$ affine. `lem-weil-pbc-affine-morphism-permanence` supplies finite-disjoint-union affineness. `lem-weil-pbc-finite-free-algebra-spectrum` applies to the algebra $D^K$, whose finite basis is displayed. `lem-weil-pbc-finite-local-on-target` assembles finiteness; `def-weil-flat-morphism` and `def-sbc-locally-finite-presentation` assemble the other local properties. Freeness and the group axioms verify the equivalence-relation hypothesis in all test schemes.
3. `lem-a1-finite-flat-affine-relation-quotient` supplies exactly the local represented fppf quotient, its $U_i$-structure, finite locally free surjection, and kernel pair. Both schemes in the relation are affine and both maps are finite locally free by step 2.
4. The sheafification criterion and universal property apply on the category over $U_i$, since every covering and refinement stays over $U_i$. The quoted Yoneda statement identifies maps between represented functors. The open representing the pulled-back subfunctor is displayed explicitly. No open-image theorem for algebraic spaces is assumed.
5. `lem-pc-schemes-criterion` has precisely the sheaf, representable-subfunctor, open-immersion and covering hypotheses verified in step 4. `lem-galois-yoneda-fully-faithful` turns the actual orbit natural transformation into the required scheme morphism.
6. `lem-weil-pbc-finite-local-on-target` applies to the open cover by the $M_i$. The definitions of flatness, local finite presentation, and finite local freeness supply the remaining assertions. `lem-weil-pbc-fpqc-representable-descent` glues the local inverse morphisms, with compatibility following from uniqueness of inverses on every overlap.
7. `def-pc-fppf-site` recognizes $q$ as a covering; `lem-trf-fppf-covering-base-change` makes $q'$ a covering. `lem-weil-pbc-finite-morphism-permanence` supplies finiteness of $q'$, so the finite-locally-free definition applies. The kernel-pair base change is written using the actual fibre-product universal property from `def-pc-fibre-product`.
8. `lem-trf-fppf-covering-base-change` gives local lifts on the displayed cover for each section; the kernel-pair comparison gives injectivity on orbit classes. These verify both hypotheses of `lem-cbc-set-presheaf-sheafification-local-bijection`. The target representable is a sheaf by step 1.
9. `def-weil-pbc-sheafification` extends the invariant natural map uniquely, and `lem-galois-yoneda-fully-faithful` gives the factorization as an actual scheme morphism. Invariance under locally constant group elements is checked piecewise on their clopen fibres. The target is an arbitrary scheme, for which step 1 already proved the needed sheaf property.

All steps are shorter than 2000 characters. The non-elementary content is cited explicitly. The only off-unit non-Mathlib proof tools are the affine-relation quotient, open-subfunctor scheme criterion and finite-free algebra spectrum lemma, each declared in `split_report.tool_uses`; these are generic geometric tools in the recorded alteration auxiliary branch, not replacements for a unit-level perverse/Fourier argument. I read delivery-errors B–E and checked statement self-containment, dependency scope, exact citation statements, non-circularity, new-node avoidance and the hypotheses in each application. No statement dispute was found.
