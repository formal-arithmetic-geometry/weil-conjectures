Files written:
- `dag/nodes/sec-picard-framework/lem-pc-derived-qcoh-perfect-generation.json` (statement, split)
- `dag/nodes/sec-picard-framework/lem-pc-perfect-generation-affine-base.json` (statement-only, Mathlib no match)
- `dag/nodes/sec-picard-framework/lem-pc-perfect-generation-open-induction-step.json` (statement-only, Mathlib no match)
- `dag/nodes/sec-picard-framework/lem-pc-perfect-generation-qcqs-induction-principle.json` (statement-only, Mathlib no match)

Attachments: none. No `WANTED` entry: the Stacks source text was available in `/home/ubuntu/c1-stacks-review/perfect.tex`.

The project source was searched for the blueprint tag and relevant declarations; no sorry-free Lean declaration states this item. The source theorem is `theorem-bondal-van-den-Bergh` in `perfect.tex`. Its affine case is represented by the affine-base child. Its induction step constructs an extension of the generator and a Koszul complex on the affine complement; this is represented by the open-induction child. The final invocation of the Cohomology of Schemes induction principle is represented by the qcqs induction-principle child. Each item proof step cites the exact child statement quoted in `citations.json`, and all hypotheses (quasi-compactness, quasi-separatedness, affine open, and quasi-coherent derived category) are carried in the statements.

## Review by H1

I read the full Stacks proof of `theorem-bondal-van-den-Bergh`, including the affine base case, the construction over an affine-open cover, and the appeal to `coherent-lemma-induction-principle`. I checked that the item statement matches the localizing formulation imported in the DAG, while the source theorem gives the stronger single-perfect-generator conclusion. The three child statements are strictly smaller: affine generation, one affine-open induction step, and the abstract qcqs induction principle. I checked every item step against the corresponding child statement and copied each citation verbatim into `citations.json`. The node's imported `unit` metadata says Serre duality, which does not match this item's perfect-generation statement; I preserved the item's source and documented this metadata inconsistency rather than changing the mathematical statement. Mathlib searches were run for the item and each child with LeanFinder, Loogle, and grep; no scheme-level theorem matched.

What could not be completed: the delivery dry run still needs to be run from the sandbox and any mechanical issues repaired.

## Second reading by H1

- Item statement: checked against Stacks Tag 09IS (`perfect.tex`, theorem-bondal-van-den-Bergh), including qcqs hypotheses and the generator formulation; verdict: the imported localizing-category formulation is weaker than the source's single-generator formulation but is the stated DAG target and is implied by it.
- Step 1: checked against Tag 06Z0 and the affine paragraph of Tag 09IS; the cited affine node supplies the affine derived equivalence and the vanishing criterion; verdict: valid after source-tag correction.
- Step 2: checked against the induction paragraph of Tag 09IS and its cited Tags 09IQ and 09IR; the extension, Koszul support, and orthogonality ingredients match the stated hypotheses; verdict: valid after making Q, K', and the closed support explicit.
- Step 3: checked against Cohomology of Schemes Tag 08DR; the affine base and affine-open gluing hypotheses are the required induction inputs; verdict: valid after correcting the source document and tag.
- New node `lem-pc-perfect-generation-affine-base`: checked for B1--B7, including affine scheme, derived category, perfect object, and generator definitions; tested on a field and the zero ring; verdict: statement-only and properly smaller than the item.
- New node `lem-pc-perfect-generation-open-induction-step`: checked for B1--B7 and against Tags 09IS, 09IQ, and 09IR; tested on an affine scheme with U=X and on the empty complement; verdict: repaired to state the actual extension and Koszul construction rather than an undefined phrase.
- New node `lem-pc-perfect-generation-qcqs-induction-principle`: checked for B1--B7 against Tag 08DR; tested on affine X and X empty; verdict: statement-only induction principle with self-contained P and qcqs hypotheses.

## Duplicate repairs

## Not duplicates

- `lem-pc-perfect-generation-affine-base` vs `lem-pc-affine-qcoh-derived-equivalence`: both use Tag 06Z0, but the former is the generator vanishing criterion (using that A generates D(A)), while the latter only states the affine derived equivalence and shift identification; the former is retained for the theorem's generator step.
- `lem-pc-perfect-generation-qcqs-induction-principle` vs `lem-sc-invert-s-cohomology-induction`: both use Tag 08DR, but the former states the theorem-specific property on all qcqs schemes with the single affine-open implication, while the latter is the broader induction on quasi-compact opens requiring separate hypotheses for the overlap; the former is retained as the theorem's exact induction input.
- `lem-pc-perfect-generation-qcqs-induction-principle` vs `lem-sc-invert-s-cohomology-separated-induction`: the new node handles arbitrary qcqs schemes and the theorem's gluing implication, whereas the existing node handles only separated quasi-compact opens as the first subinduction; neither is a special case of the other.
- `lem-pc-perfect-generation-qcqs-induction-principle` vs `lem-kun-0f10`: the new node packages the Bondal--van den Bergh property and its affine-open premise, whereas `lem-kun-0f10` is a distinct topological induction lemma with different overlap premises; neither states the other's conclusion.

Changes made: corrected all Stacks sources to stable tags (`09IS`, `06Z0`, `08DR`); fixed the item's `created.item` ownership metadata; and made the open induction node's objects and support explicit. The imported unit metadata still names Serre duality, which is unrelated to this item, so it was left unchanged as maintainer-owned metadata.
