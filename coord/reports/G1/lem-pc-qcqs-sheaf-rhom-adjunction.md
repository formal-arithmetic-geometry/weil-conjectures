1. Files written:

- `dag/nodes/sec-picard-framework/lem-pc-qcqs-sheaf-rhom-adjunction.json` — statement node, split into four proof steps, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-pc-sheaf-rhom-projection-formula.json` — statement-only child, no Mathlib match.
- `citations.json` — verbatim statement excerpts for every cited node in every step.

2. Attachments: none.

3. WANTED: `literature/stacks-project/duality.tex`, Tag 0A9Q and Tag 0B6I, for `lem-pc-qcqs-sheaf-rhom-adjunction`.
WANTED: `literature/stacks-project/cohomology.tex`, the internal-Hom projection-formula remark cited in Tag 0B6I, for `lem-pc-sheaf-rhom-projection-formula`.

4. The imported item had no proof. The source proof's first comparison morphism was not represented by an existing DAG node, so I created a statement-only node for that canonical map; the remaining proof facts were matched to existing nodes. The source's five Hom equalities were retained as one explicit chain, with the projection formula supplying the fourth equality. No item clause was moved into a child node.

5. Nothing remains unfinished in the split. The local source checkout was used because the Stacks files are not present under this repository's `literature/` directory.

## Review by G1

I read the item, its blueprint ancestor `lem-sc-finite-duality`, and the local Stacks text for Tag 0A9Q together with Tag 0B6I. The item statement has the same qcqs hypotheses as the source and the existing right-adjoint and coherator nodes. For Step 1 I checked that the new child states exactly the canonical internal-Hom morphism used as the first arrow in the source and that the right-adjoint node states the counit data used for postcomposition. Step 2 uses only the coherator node's stated right-adjoint property. Step 3 cites the stated derived pullback/direct-image Hom bijection, the stated tensor/internal-Hom bijection, the stated right adjoint to restricted `Rf_*`, and the stated projection formula; these provide each of the five displayed equalities, with tensor symmetry used only to reorder factors. Step 4 uses the naturality clauses stated by the projection and internal-Hom nodes and the adjunction node's right-adjoint conclusion for the Yoneda conclusion. I checked the hypotheses at each use: X and Y are qcqs schemes, f is qcqs, L and K are in the indicated quasi-coherent derived categories, and the test object M is quasi-coherent. I tested the shape on the identity morphism and on an affine morphism, where the map reduces to the ordinary tensor/internal-Hom adjunction. The Mathlib searches for the item and new child were run with LeanFinder, Loogle, and Mathlib grep; only underived sheaf adjunctions appeared.

## Not duplicates

`lem-pc-sheaf-rhom-projection-formula` vs `lem-pc-qcqs-sheaf-rhom-adjunction`: the child states only the preliminary canonical internal-Hom morphism and makes no coherator-isomorphism claim; the item proves the counit composite becomes an isomorphism after applying DQ_Y.
`lem-pc-sheaf-rhom-projection-formula` vs `lem-pc-dq-coherator-adjunction`: the child constructs the internal-Hom comparison morphism, while the existing node states the coherator right adjunction and global-section detection property.
`lem-pc-sheaf-rhom-projection-formula` vs `lem-pc-global-hom-adjunction`: the child is a sheaf-level comparison before applying global sections and has arbitrary M on X; the existing node is a global RHom adjunction with derived pullback and direct image.

## Second reading by G1

- Item statement: checked against Stacks Tag 0A9Q (`lemma-iso-on-RSheafHom`) and the preceding sheafy-trace construction; qcqs hypotheses, QCoh source objects, the counit map, and the conclusion after `DQ_Y` agree hypothesis by hypothesis.
- Step 1: checked against Tag 0B6I equation (48.1.1.1), the internal-Hom comparison remark, and the stated right-adjoint counit; the cited statements provide both arrows and naturality.
- Step 2: checked against the coherator adjunction node and the proof paragraph beginning “Since DQ_Y is the right adjoint”; the arbitrary quasi-coherent test object and Hom criterion are stated with the required category.
- Step 3: checked each of the five equalities against the cited derived adjunction, tensor/internal-Hom adjunction, QCoh right adjoint, and projection-formula statements; tensor symmetry is only the explicit reordering of factors.
- Step 4: checked against the source conclusion and the cited triangle/naturality data; the Yoneda conclusion is applied in `D_QCoh(O_Y)` exactly as required.
- `lem-pc-sheaf-rhom-projection-formula`: checked against Cohomology, Remark `remark-projection-formula-for-internal-hom`; it is statement-only, self-contained, and makes no unjustified isomorphism claim.
- Small cases: identity morphism gives the identity comparison; affine schemes reduce to the ordinary tensor/internal-Hom adjunction; the source's `Y = Spec(R), X = A^1_R` example confirms that omitting `DQ_Y` would be false.

Changes made:

- Corrected the item node's `created.item` to `lem-pc-qcqs-sheaf-rhom-adjunction` so ownership metadata matches the delivered item.
- Corrected the child node's source label from the nonexistent `cohomology-remark-projection-formula-for-internal-hom` to `remark-projection-formula-for-internal-hom`, the label in `cohomology.tex`.
