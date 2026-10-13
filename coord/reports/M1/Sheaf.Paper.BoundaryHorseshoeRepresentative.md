## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.Modules.boundary_horseshoe_representative`
by an explicit composition of a lift-and-cycle theorem and a boundary-comparison theorem.
Its existing signature is byte-for-byte unchanged. Added the two helper modules
`Sheaf.Paper.BoundaryHorseshoeGlobalLift` and
`Sheaf.Paper.BoundaryHorseshoeBoundaryIdentification`.
The global-lift helper is proved using Mathlib row splitting, exactness, and cyclesMk.
The boundary comparison is the remaining open part of the original argument.
No definitions, existing statements, or existing public imports were changed.
The new global-lift module imports the cohomology and derived-category declarations
its signature needs, rather than the unrelated canonical-boundary module.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.Scheme.Modules.boundary_horseshoe_representative`
(node `lem-sc-boundary-horseshoe-representative`).

New helper proved:
`AlgebraicGeometry.Scheme.Modules.boundary_horseshoe_global_lift`
(node `stage3-boundary-global-lift`), which the first worker had left open.

New hole added and still open:
`AlgebraicGeometry.Scheme.Modules.boundary_horseshoe_boundary_identification`
(node `stage3-boundary-identification`). It has a complete source-backed proof in its
new docstring. There are no other holes in the delivered files.

This is a decomposition: one original hole closed and one new hole added, net zero
in the target import closure, not a completed axiom-free proof of the original theorem.
The item is still dependent on sorryAx through the boundary comparison and any open
upstream statements. The new global-lift theorem adds no proof hole.

## No longer needed

Removed direct proof imports of `Sheaf.CategoryTheory.Abelian.RightDerivedTriangleConnecting`,
`Mathlib.Algebra.Homology.ConcreteCategory`, and
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat` from the target module.
The boundary comparison imports the first two for its recorded proof plan; the proved
global lift imports the latter two. No whole library module is claimed pruned.

The original target node's old proof_deps are no longer direct dependencies of its
composition proof: `def-sp-injective-resolutions`,
`lem-weil-pbc-complex-ses-homology-long-exact`,
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`,
`lem-weil-pbc-derived-functor-map-via-lift`,
`lem-sc-p1-right-derived-triangle-connecting`, and
`def-sc-module-cohomology-boundary`. They are retained in the helper nodes where the
lifting proof or boundary-comparison plan uses them. The target now depends on
`stage3-boundary-global-lift` and `stage3-boundary-identification`.

## Where the brief, the DAG or earlier work was wrong

The first worker's report called the target proved without recording that two new
holes made the work a decomposition. Its new node records lacked verbatim Lean
signatures, self-contained statements, proof steps, statement dependencies and actual
Mathlib searches. Its helper docstrings lacked complete natural-language proofs and
used blueprint IDs different from the node filenames. The target node retained its
old proof rather than the composition actually written. These are repaired.

## New nodes

`stage3-boundary-global-lift`, in
`dag/nodes/sec-curve-estimates/stage3-boundary-global-lift.json`, formalizes only the
existence of the lift and cycle (original steps 1-2). Its Lean proof uses split exact
rows under additive global sections, then Mathlib's exactness and cycle lemmas.

`stage3-boundary-identification`, in
`dag/nodes/sec-curve-estimates/stage3-boundary-identification.json`, formalizes only
the original step 3, conditional on already supplied b and a satisfying the lifting
equations. It does not assert their existence and is strictly part of the original
argument. Its comparison route retains the existing right-derived triangle theorem.
No change records are needed: all existing signatures and definitions are unchanged.

## Second reading by M1

1. Compared the target file against the repository with diff. Only proof imports and
the proof body changed; its existing signature is identical. The two other modules
are new. No hidden hypothesis, weakened conclusion, changed definition or interface
change was found.
2. Read all delivered Lean code. No axiom, unsafe, opaque, implemented_by, extern,
holed definition or arbitrary data chosen from an unproved existence theorem occurs.
The sole remaining sorry is the named boundary-identification theorem.
Compilation and scratch #print axioms results are recorded below after validation.
3. Tested the helper statements mathematically at q=0, zero objects and arbitrary
compatible horseshoes. Injectivity splits every row; exactness and d squared=0 give
an actual cycle. The boundary formula holds for any permitted lift, whose change
alters a by a boundary. Both statements are true and strictly smaller parts of the
original theorem. Searched Mathlib using leanfinder, loogle, leansearch and grep with
queries different from the first worker, and searched lean/Sheaf and the upstream
library. The existing splitting and cycle lemmas close the lift helper; the existing
right-derived comparison and concrete snake formula are ingredients, not duplicates
of the remaining bundled sheaf boundary statement. Leansearch was unavailable and
is recorded as such rather than assigned an invented verdict.
4. Kept the original resolution-to-boundary route and used the shortest Mathlib route
for lifting. Removed the target's unused direct proof imports and listed every old
proof dependency above. The unit sk-thm-curveestimate realizes its statement by
thm-sc-proper-cohomology and has no realized steps; this delivery does not change or
bypass a realized unit node.
5. Checked all three node records against the Lean. The target records the two-helper
composition; the lift node records its actual splitting/exactness proof; the open
comparison node records precisely the remaining snake/derived-triangle comparison.
Their proof_deps equal the union of their steps' uses. Both new nodes have source,
searches, original-node provenance, chapter/unit and verbatim Lean signatures.

Second reading changed: proved the global-lift helper, completed both new docstring
proofs, repaired blueprint IDs and line-width warnings, completed the new DAG records,
updated the target proof record, pruned direct proof imports, and corrected progress
accounting. The target's composition proof was retained.

Validation: all three delivered modules compiled without errors or warnings in the
successful deliver3.py dry run (commit 469cd8d046, review class CODEX because it adds
nodes and modules). The scratch copy at
`scratchpad/Sheaf.Paper.BoundaryHorseshoeRepresentative/lean/Sheaf/Paper/AxiomReview.lean`
compiled successfully and printed:

- `boundary_horseshoe_global_lift`: propext, Classical.choice, Quot.sound only.
- `boundary_horseshoe_boundary_identification`: those three plus sorryAx.
- `boundary_horseshoe_representative`: those three plus sorryAx.

The source review used [Stacks Tag 0117](https://stacks.math.columbia.edu/tag/0117)
for the snake construction and
[Tag 013T](https://stacks.math.columbia.edu/tag/013T) for compatible injective resolutions,
with [Tag 015B](https://stacks.math.columbia.edu/tag/015B) for the derived-functor route.
