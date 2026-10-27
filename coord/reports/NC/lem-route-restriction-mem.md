# Stage-1 worker report: lem-route-restriction-mem

## Files written

- `dag/nodes/sec-nagata-compactification/lem-route-restriction-mem.json`: item split in place; no new nodes.
- `citations.json`: the verbatim citation for proof step 1.
- `searches.jsonl`: preserved by `msearch.py` for all five searches run on 2026-10-27.

## Attachments

The live declaration `AlgebraicGeometry.RelativeProjAlgebra.restriction_mem` in `lean/Sheaf/AlgebraicGeometry/RelativeProjData.lean:109-112` still has `sorry`, so it is not an attachment. No sorry-free slopmaster2 declaration was found.

## WANTED

None.

## Not duplicates

`lem-route-restriction-mem` vs existing DAG nodes: no existing node states preservation of the image defining `sectionGrade` under affine restriction; the sibling route nodes (`sectionGrade_one`, `sectionGrade_mul`, `sectionGrade_internal`, `unit_mem`, and `irrelevant_le`) have different conclusions.

## What was checked and corrected

The generated record was provisional and omitted the objects and hypotheses. I replaced it with a self-contained statement for a scheme, a quasi-coherent graded algebra, its homogeneous sheaves and decomposition, affine opens `W ⊆ V`, a degree `n`, and an element in the image subgroup. The displayed Lean conclusion is unchanged. I filled the blueprint ancestor/place and `same_as` fields, set the proof origin to the current blueprint, and recorded the actual Mathlib search results. No new node was created because the proof is exactly a range witness transported across one sheaf naturality square; making that witness a separate node would restate this item.

## Review by NC

I read the current blueprint definition `literature/blueprint/latest/blueprint/sec-nagata-compactification/sk-def-nagata-admissible/def-nagata-relative-proj.md`, the ancestor proof `lemma-nagata-relative-proj-exists.proof.md` (especially its local-squares paragraph), the imported DAG definition `def-nagata-relative-proj`, and the source declaration and definition in `lean/Sheaf/AlgebraicGeometry/RelativeProjData.lean:69-71,105-112`. The source defines `sectionGrade` as the range of the degree-(n) homogeneous-sheaf inclusion and states `restriction_mem` with exactly the affine-open restriction map shown in the node.

Step 1 uses `def-weil-pbc-graded-sheaf-structures`; its cited statement explicitly says that the graded sheaf operations are “compatible with restriction.” I checked that the step only uses this naturality square and the elementary definition of image membership: a witness `b` at `V` restricts to a witness at `W`. The hypotheses `W ≤ V`, arbitrary `n : ℕ`, and arbitrary `a` with image membership are all retained. Small cases `W = V`, `n = 0`, the empty scheme, and a zero homogeneous component reduce to the same witness argument; no quasi-coherence or nonemptiness assumption is silently used in the proof.

The Mathlib searches were run with `msearch.py` and logged verbatim in `searches.jsonl`: LeanSearch and LeanFinder returned only generic section/naturality declarations, Loogle reported its pattern identifier unavailable, and the two Mathlib grep searches found no exact project theorem. The server checks `check_dag` and `review_split` both passed before this report was written.

## What remains

No unfinished split work remains for this item.
