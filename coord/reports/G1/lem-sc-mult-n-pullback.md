1. Files written:

   - `dag/nodes/sec-abelian-varieties/lem-sc-mult-n-pullback.json` — item split; no new nodes.

   - `citations.json` — citation for the cube relation used in step 1.

2. Attachments: none.

3. WANTED: none.

4. The imported Lean declaration `AlgebraicGeometry.nonempty_iso_overPullback_npow_id` is not attachable because its sorry-free body rests transitively on sorried declarations. The imported proof had an unset `elementary` value and no source on its induction step; these are now explicit. No statement or dependency was changed. The existing `thm-sc-theorem-of-cube` node was searched and used; no duplicate or smaller node was created.

5. Nothing remains unfinished.

## Review by G1

I read the item source in the blueprint unit `_section.md`, the imported item node, and the source declaration in `WeilConjectures/AlgebraicGeometry/AbelianVariety/Cube.lean` (theorem at lines 142–199). The item statement agrees with the declaration's mathematical content: an abelian variety over a field, an invertible symmetric module, and the `n`-fold multiplication pullback is the `n^2` tensor power. I also read `thm-sc-theorem-of-cube.json`; its statement supplies exactly the seven-term cube isomorphism quoted in `citations.json` and used by step 1.

Step 1 substitutes `(x,x,-x)` and `(x,x,[n-1]x)` into that seven-term relation. The listed partial sums are direct applications of the definitions of the group law and multiplication map; symmetry identifies `[-1]^* N` with `N`, yielding the `n=2` relation and the displayed recurrence. Step 2 uses only the recurrence, the base cases `n=1,2`, cancellation in tensor powers of an invertible module, and the arithmetic identity `4+2n^2-2-(n-1)^2=(n+1)^2`; these are elementary induction and rearrangement, so it is marked elementary and cites no additional node. I checked the small cases `n=1` and `n=2` explicitly against the statement and recurrence.

The item and theorem-of-the-cube sources were checked for their hypotheses: the same abelian variety and field occur throughout, and invertibility is present where the cube relation is applied. The required Mathlib searches were run for the item (LeanFinder, Loogle, grep, and unavailable LeanSearch) and recorded verbatim in the node. No new node was warranted because the proof's only non-elementary input is already the existing cube node.

## Second reading by G1

- Item statement: checked against Stacks Project Tag 0BFF, Lemma 39.9.7, including the field, abelian variety, invertibility, symmetry hypothesis, and restriction $n\geq1$; verdict: agrees hypothesis by hypothesis.
- Step 1: checked against Tag 0BFF and `thm-sc-theorem-of-cube`; the two pullback maps, all seven partial sums, the symmetry substitution, and the displayed recurrence are correct; verdict: passes, with the cube relation as its only non-elementary citation.
- Step 2: checked against the recurrence and the base cases $n=1,2$; cancellation uses invertibility, and $4+2n^2-2-(n-1)^2=(n+1)^2$; verdict: elementary induction, with the induction step applied for $n\geq2$.
- New nodes: none; existing `thm-sc-theorem-of-cube` was checked for the quoted statement, and no duplicate or Mathlib leaf is needed.
- Edge cases: $n=1$ gives the identity pullback and first tensor power; $n=2$ is the first cube calculation; $n=0$ is intentionally excluded because the stated formula is not valid for an arbitrary invertible module.

Changes made: added `def-sc-invertible-module` to `stmt_deps`, since invertibility is a notion used by the item statement; filled `blueprint.from` with the item’s two realized proof locations. No mathematical statement or proof step was changed.
