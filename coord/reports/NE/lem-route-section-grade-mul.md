# Stage-1 report: lem-route-section-grade-mul

Files written:

- `dag/nodes/sec-nagata-compactification/lem-route-section-grade-mul.json` — statement node, no new nodes, Mathlib verdict: generic graded multiplication results only; no direct match.
- `citations.json` — empty because the proof uses only the `RelativeProjAlgebra` datum and elementary range unpacking, with no DAG node citation.

Attachments: none. The live declaration `AlgebraicGeometry.RelativeProjAlgebra.sectionGrade_mul` in `lean/Sheaf/AlgebraicGeometry/RelativeProjData.lean:81-84` contains `sorry`, so it is not an attachment. No prior archived attempt existed.

WANTED: none.

The provisional statement was replaced by a self-contained natural-language statement that explains `sectionGrade` as the range of the degree-piece inclusion and records the `mul_eq` compatibility used by the proof. No statement clause was changed: the quantifiers and conclusion agree with the Lean declaration. The item is a single elementary range-witness argument, so creating a helper node would have duplicated a clause of the item. I searched the DAG and current blueprint for an existing section-grade multiplication node; none exists. Mathlib searches were run with LeanFinder, Loogle, grep, and LeanSearch. They returned generic `SetLike.GradedMul.mul_mem`/`SetLike.mul_mem_graded` and related direct-sum lemmas, but these require a grading instance that is constructed only after `sectionGrade_mul`; none states this range-defined theorem directly.

## Review by NE

I read the current item, the source declaration and docstring in `lean/Sheaf/AlgebraicGeometry/RelativeProjData.lean`, and the current blueprint definition `literature/blueprint/latest/blueprint/sec-nagata-compactification/sk-def-nagata-admissible/def-nagata-relative-proj.md`. The source structure supplies homogeneous piece sheaves, the direct-sum decomposition, and `mul_eq`; the theorem's hypotheses are exactly two affine-section range memberships. For the only proof step I checked that each membership supplies witnesses in the degree-m and degree-n piece, that `mul_eq` identifies the image of their graded product with `a*b`, and that the graded product has degree `m+n`, yielding the required range witness. This checks edge cases m=0, n=0, and zero witnesses as well. The step is marked elementary because it is a direct unpacking of ranges followed by one structure-field equality. I kept `proof_deps` empty and therefore `citations.json` empty; no cited DAG statement is being used. I also verified that the declaration remains sorried and that no sorry-free declaration in the source or slopmaster2 checkout states this item.

Nothing remains unfinished in the split itself. The required dry run and delivery are the next operations.
