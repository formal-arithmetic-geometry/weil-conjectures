Files written:

- `dag/nodes/sec-abelian-varieties/thm-sc-theorem-of-cube.json` (statement, split)
- `citations.json`

Attachments: `AlgebraicGeometry.nonempty_iso_cube` belongs to `thm-sc-theorem-of-cube`, but it is not attachable because its proof rests on sorried declarations.

WANTED: none.

The imported item was not attachable: the source declaration has no local `sorry`, but its audit exposes the general slice theorem and lower declarations whose proofs are still sorry-backed. The general cube theorem is the non-elementary theorem being applied inside the item's own proof, so creating a helper node would restate a clause of the item (D1/D2); it was removed after the delivery preflight identified that issue. No Mathlib theorem supplies the result.

## Not duplicates

No new node remains. The attempted helper was removed because it restated the general theorem used as the item's proof step.

## Review by M1

I read the item's blueprint proof and the source declarations in `WeilConjectures/AlgebraicGeometry/AbelianVariety/Cube.lean` and `TheoremOfCube.lean`. The item step forms the alternating tensor product M and applies the general cube theorem on the three slices. It cites `lem-sc-abelian-variety-characterization` for smoothness, properness, connectedness, and geometric integrality of the abelian variety; the unit section supplies the required rational point. I checked each slice calculation: setting any one coordinate to the unit reduces all seven partial sums to the same three maps, with the unit pullback of an invertible module trivial, so M restricts to the structure module. The edge case of a trivial line bundle gives the identity relation. The source declaration `nonempty_iso_cube` (lines 98-126) is sorry-free locally but rests on the sorried general cube helpers in `TheoremOfCube.lean`, so it cannot attach. The exact characterization quote in `citations.json` was copied from the cited node statement.

## Second reading by M1

- Item statement: checked against the blueprint node `thm-sc-theorem-of-cube` and Stacks Tags 0BFE and 0BF4; the seven partial-sum factors and hypotheses agree.
- Step 1: checked against the blueprint proof and `AlgebraicGeometry.nonempty_iso_cube`; the alternating tensor product, general cube application, and all three unit-slice cancellations are stated. The abelian-variety definition, invertible-module definition, and characterization lemma are all cited by node statement.
- New nodes: none; the attempted helper was removed because it restated the general cube conclusion and was transitively sorry-backed in Lean.
- Small cases: for `\\mathcal L = \\mathcal O_A` the relation is the identity; on each unit slice `e^*\\mathcal L \\cong \\mathcal O` makes the seven factors cancel. The empty scheme and zero-dimensional edge cases are excluded by the abelian-variety definition and its unit section.
- Changes: added `def-sc-abelian-variety` and `def-sc-invertible-module` to step 1 and `proof_deps`, with exact statement quotes in `citations.json`, because the proof uses those hypotheses directly.
