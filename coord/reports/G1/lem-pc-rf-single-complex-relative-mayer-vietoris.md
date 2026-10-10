Files written:

- `dag/nodes/sec-picard-framework/lem-pc-rf-single-complex-relative-mayer-vietoris.json` (split item)
- `dag/nodes/sec-picard-framework/lem-pc-rf-mv-triangle-naturality.json` (statement-only unsplit node)

Attachments: none.

WANTED: none.

The Lean source was searched for the item id, its key notions, and the blueprint tag; no project declaration states this result. The existing derived Mayer–Vietoris triangle node was searched for and used rather than recreated. The new node is strictly narrower than the item: it asserts only that the canonical comparison maps form a morphism of triangles, without asserting any component is an isomorphism. Mathlib searches were run for both the item and new node; the generic Mayer–Vietoris and triangle declarations do not state the scheme-level relative comparison, and LeanSearch was unavailable.

## Not duplicates

lem-pc-rf-mv-triangle-naturality vs lem-pc-rf-single-complex-relative-mayer-vietoris: the new node asserts only existence and commutativity of the Mayer–Vietoris triangle morphism; the item concludes that its X component is an isomorphism from local hypotheses.
lem-pc-rf-mv-triangle-naturality vs lem-pc-rf-single-complex-qcqs-induction: the existing node uses the relative gluing result as a black-box induction step and concludes global base change; the new node supplies the triangle naturality underlying that gluing step and has no isomorphism conclusion.
lem-pc-rf-mv-triangle-naturality vs lem-pc-rf-single-complex-affine-base-change: the existing node is the affine stalkwise/module criterion; the new node concerns naturality of derived Mayer–Vietoris triangles for arbitrary qcqs open covers.
lem-pc-rf-mv-triangle-naturality vs lem-pc-rf-base-change-single-complex-criterion: the existing node states the full single-complex base-change criterion from stalk hypotheses; the new node is only the triangle-morphism compatibility used in its qcqs induction proof.

## Review by G1

I checked the item against `literature/stacks-project/perfect.tex`, Tag 0DJ9, and the cited relative Mayer–Vietoris construction in `literature/stacks-project/cohomology.tex`, Tag 08BV. Step 1 cites the existing node whose statement supplies the distinguished triangles for a qcqs scheme covered by two quasi-compact opens. Step 2 cites the new naturality node, whose statement explicitly supplies the three comparison components and says they form a morphism of those triangles. Step 3 uses the local hypotheses exactly for U, V, and U intersect V; the direct sum of the first two is an isomorphism, and the existing Mathlib leaf `lem-sf-triangle-morphism-iso` supplies two-out-of-three for the triangle morphism. Step 4 is the identification of the X component with the displayed canonical composite and is elementary. I verified all hypotheses: U and V are quasi-compact, their intersection is quasi-compact, and the base-changed cover has the same form. I also checked that no child node duplicates an existing DAG statement and that the new node does not restate the item's conclusion.

## Second reading by G1

- Item statement: checked against perfect.tex Tag 0DJ9; the cartesian square, qcqs hypotheses, open-cover hypotheses, local comparison maps, and global conclusion all match the source induction diagram.
- New node `lem-pc-rf-mv-triangle-naturality`: checked against perfect.tex Tag 0DJ9 and cohomology.tex Tag 08BV; it states only the functorial morphism of the relative Mayer–Vietoris triangles and includes the needed derived-category hypotheses.
- Step 1: checked against cohomology.tex Tag 08BV and `lem-pc-derived-mayer-vietoris-triangle`; the cited statement supplies both triangles and the cover hypotheses are in force.
- Step 2: checked against the Tag 0DJ9 commutative diagram and the naturality node; the three components are exactly the displayed comparison maps, including the direct-sum middle component.
- Step 3: checked against Tag 0DJ9 and `lem-sf-triangle-morphism-iso`; the local isomorphisms make the direct-sum middle map an isomorphism, so two-out-of-three gives the X component.
- Step 4: checked against the definition of `alpha_X` in the new node and the item statement; the identification is immediate and elementary.
- Edge cases: the statement is conditional on an actual two-open cover and the three local comparison maps, so empty or degenerate schemes introduce no unstated conclusion.

Changes: none to the worker's node statements or proof; added this audit section and verified the existing citations and Mathlib search records. The delivery dry run passed unchanged.
