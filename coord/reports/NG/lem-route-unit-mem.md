# Stage-1 worker report: lem-route-unit-mem

## Files written

- `dag/nodes/sec-nagata-compactification/lem-route-unit-mem.json`: statement split, no new nodes; Mathlib searches found only general graded-one declarations and no exact project-specific match.

## Attachments

None. `AlgebraicGeometry.RelativeProjAlgebra.unit_mem` in `lean/Sheaf/AlgebraicGeometry/RelativeProjData.lean` still has a `sorry`, so it is not an attachment.

## WANTED

None. The proof is an elementary unpacking of available input definitions; no missing reference is used.

## What was wrong or provisional

There were no matching abandoned-attempt directories, and the active sandbox contained no item node, report, or earlier search log before this session. The live node was a provisional machine-made record with an implicit `RelativeProjAlgebra` context and only a one-line proof sketch. I replaced it with a self-contained statement spelling out the graded pieces, direct-sum inclusion, section ring, and range definition of `sectionGrade`. The statement expresses exactly the Lean theorem `AlgebraicGeometry.RelativeProjAlgebra.unit_mem`; no hypothesis or conclusion was changed. The blueprint has no separate unit-membership node, so no duplicate was found. The related `sectionGrade_one` node is a different conclusion (membership of the ring unit, rather than the image of an arbitrary base section) and is not used.

## What could not be finished

Nothing. No Lean files were written and no compiler or build tool was run, as required for stage 1.

## Review by NG

I read the item source declaration and its surrounding definitions in `lean/Sheaf/AlgebraicGeometry/RelativeProjData.lean`, especially `RelativeProjAlgebra.sectionGrade`, `RelativeProjAlgebra.unit_eq`, and the `unit_mem` signature at lines 131–136. I also read the existing `def-nagata-relative-proj` node and the current blueprint definition and existence proof. The rewritten statement introduces the scheme, graded algebra datum, homogeneous pieces, section ring, image subgroup, and unit compatibility needed by the Lean signature; its conclusion is exactly the displayed membership statement.

The sole proof step uses no external node: it unfolds the range defining `sectionGrade V 0`, chooses the degree-zero graded-unit section applied to `r`, and invokes `unit_eq` to identify its image with the algebra-structure section. This is elementary once the datum and range definition are in view, so `uses` and `proof_deps` are empty; accordingly `citations.json` is empty. I checked the neighboring `sectionGrade_one` and `sectionGrade_mul` route nodes to ensure this item is neither a restatement of their conclusions nor dependent on them. I tested the edge cases conceptually: `r = 0`, the zero graded piece, and an affine open with trivial section ring all reduce to the same range witness supplied by `unit_eq`. Mathlib searches were run through `msearch.py` for LeanSearch, LeanFinder, Loogle, and Mathlib grep. I read `SetLike.algebraMap_mem_graded` at Mathlib/Algebra/DirectSum/Internal.lean:61–64: it assumes a family of base-ring submodules and `GradedOne`. The item instead concerns the specific additive-subgroup image constructed from sheaf morphisms. Building those extra instances is unnecessary: the explicit range witness proves the item directly, without using the sorried `sectionGrade_one` or `sectionGrade_internal`. I retained the actual search log and recorded the initial invalid Loogle identifier and redundant Mathlib directory prefixes as inconclusive, then corrected both. No unavailable query is counted as evidence of absence.

The only statement dependencies are the existing relative-Proj input and graded-sheaf structure definitions. The relative-Proj statement supplies the underlying graded algebra sheaf presentation; the graded-sheaf definition supplies the linear unit into the zeroth homogeneous piece. The compatibility with the chosen decomposition is written explicitly in the item as part of the existing `RelativeProjAlgebra` datum, rather than attributed to a theorem these definition nodes do not state. Since the proof step cites no node, there is no node quote to fabricate. No off-unit proof tool is used.

Against delivery-errors B–E: the statement is self-contained and uses TeX; no new unsplit node, duplicate lemma, or clause relabelling was created. The proof is under 2000 characters, contains the full witness argument, and assumes neither an affine intersection nor a base-change or finiteness property. In particular it does not use the relative-Proj structural-map conclusion as a proof of itself. The empty scheme/empty affine open and zero algebra cause no problem; for a grading concentrated in degree zero it gives the same unit-map image. It does not assert that the structural map is an isomorphism, and it applies when the degree-zero algebra is larger than the base ring. No statement dispute was necessary.
