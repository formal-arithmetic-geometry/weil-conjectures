1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-derived-hom-mayer-vietoris.json` — split item with two proof steps.
- `dag/nodes/sec-picard-framework/lem-sc-derived-mayer-vietoris-triangle.json` — statement-only child, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-derived-open-shriek-derived-adjunction.json` — statement-only child, no Mathlib match.
- `citations.json` — verbatim quotes for every cited step dependency.

2. Attachments: none. No sorry-free slopmaster2 declaration states Tag 08BW.

3. WANTED: none; the obtained Stacks source at `/home/ubuntu/c1-stacks-review/cohomology.tex` was read directly for Tags 08BV, 08BT, and 08BW.

4. The imported item had no proof. The proof of Tag 08BW uses the distinguished lower-shriek Mayer–Vietoris triangle and the derived extension-by-zero/restriction adjunction; both are genuine independent inputs for an arbitrary ringed space and were added as statement-only children. The existing scheme-specific `lem-pc-derived-mayer-vietoris-triangle` was not reused because its hypotheses are restricted to qcqs schemes and quasi-coherent objects. The exactness of Hom into a distinguished triangle is the existing Mathlib leaf `lem-weil-pbc-hom-into-triangle-exact`.

## Review by E1

I read the item source, Cohomology Tag 08BW (Lemma 20.33.3), and the preceding triangle source Tag 08BV and adjunction source Tags 08BS/08BT in `cohomology.tex`. The item statement agrees with 08BW: the cover is by two opens, the displayed terms are derived Hom on X, U, V, and U intersection V, the middle arrow is restriction difference, and the preceding term is negative Ext. I also searched the Lean source for the item id, the blueprint tag, and derived-Hom/Mayer–Vietoris names; no exact sorry-free declaration exists.

Step 1 uses the new triangle statement, which explicitly supplies the four triangle vertices and identifies its maps, and the existing Mathlib leaf, whose statement gives exactness of Hom into a distinguished triangle. The triangle hypotheses are exactly a ringed space and an open cover. Step 2 uses the new derived adjunction statement for each open inclusion and the triangle statement for the difference/counit descriptions; these statements say precisely the identifications and map formula used. No uncited non-elementary fact is hidden in either step.

For the new triangle child I checked the arbitrary ringed-space hypotheses and the extension-by-zero objects against Tag 08BV; for the adjunction child I checked exact extension by zero and restriction against the existing ringed-space adjunction node and the derived adjunction conclusion against Tag 08BT. Both children were searched with LeanFinder, Loogle, grep, and LeanSearch; LeanSearch was unavailable and recorded as such. Small cases checked were U=X, V=X, empty intersection, and X empty; the triangle and exact sequence reduce to the expected identity or zero cases. The citations file quotes exact text from every cited node.

## Not duplicates

lem-sc-derived-mayer-vietoris-triangle vs lem-pc-derived-mayer-vietoris-triangle: the new node is for arbitrary ringed spaces and all derived objects with extension by zero, while the existing node is only for qcqs schemes and quasi-coherent derived objects using derived direct images.
lem-sc-derived-open-shriek-derived-adjunction vs lem-pc-ringed-spaces-derived-adjoint: the new node concerns exact extension by zero and restriction for an open inclusion of ringed spaces, while the existing node concerns derived pullback and direct image for scheme morphisms.
lem-sc-derived-open-shriek-derived-adjunction vs lem-sc-derived-hom-mayer-vietoris: the new node states the derived extension-by-zero/restriction adjunction used as an input; the existing item states the Mayer–Vietoris exact sequence that uses it.
lem-sc-derived-open-shriek-derived-adjunction vs lem-pc-restrict-derived-direct-image-open: the new node is an adjunction for exact extension by zero on arbitrary ringed spaces, while the existing node is restriction of derived direct images along arbitrary scheme morphisms.
lem-sc-derived-open-shriek-derived-adjunction vs lem-sc-derived-open-restriction-adjunction-exact: the existing node proves the underived exact adjunction on module sheaves; the new node is the induced derived-category Hom bijection.
lem-sc-derived-open-shriek-derived-adjunction vs lem-sc-derived-k-injective-restrict-open: the existing node proves restriction preserves K-injective complexes; the new node identifies derived Hom via extension-by-zero adjunction.
lem-sc-derived-open-shriek-derived-adjunction vs lem-sc-derived-internal-hom-restrict-open: the existing node concerns restriction of derived internal Hom; the new node concerns the external Hom adjunction with extension by zero.

## Second reading by E1

- Item statement: checked against Cohomology Tag 08BW (Lemma 20.33.3), hypothesis by hypothesis; revised the derived-category and ringed-space dependencies to use the generic definitions rather than the scheme-only definition.
- Step 1: checked against Tag 08BW's use of Tag 08BV and Derived Categories Lemma 0149; found that the original covariant Hom leaf had the wrong variance, and replaced it with the existing contravariant exactness node `lem-weil-pbc-hom-out-of-triangle-exact`.
- Step 2: checked the three adjunction identifications and the restriction-difference map against Tags 08BT and 08BV; the cited statements supply the required bijections and map descriptions.
- `lem-sc-derived-mayer-vietoris-triangle`: checked against Tag 08BV; statement now defines the generic derived category of module sheaves and all ringed-space hypotheses.
- `lem-sc-derived-open-shriek-derived-adjunction`: checked against Tags 08BS and 08BT; statement now uses the generic module-sheaf derived categories and exact functor hypotheses.
- Existing `lem-weil-pbc-hom-out-of-triangle-exact`: checked by grep and direct inspection; its two clauses supply exactly the contravariant Hom exactness needed, so no duplicate node was retained.

Changes made: corrected the item and child-node dependencies and statements for arbitrary ringed spaces, replaced the incorrectly covariant Hom citation in step 1 with the existing contravariant node, updated `proof_deps` and citations, and removed a duplicate candidate after the duplicate check. Small cases U=X, V=X, empty intersection, and X empty reduce to identity or zero sequences as expected.
