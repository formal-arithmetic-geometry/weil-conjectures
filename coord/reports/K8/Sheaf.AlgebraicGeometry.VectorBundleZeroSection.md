## What changed

Completed three proofs in `Sheaf.AlgebraicGeometry.VectorBundleZeroSection`:
`augmentation_spec` uses the symmetric-algebra universal property and induction;
`zero_spec` uses `Over.w` and the closed-immersion criterion for a section of a
separated morphism; `affineChart_naturality` uses naturality of `toSpecΓ`, the
algebra isomorphism, and the sheafification unit. Added the proof-only import
`Mathlib.AlgebraicGeometry.Morphisms.Separated`. Updated the definition node's
proof record to distinguish these arguments from the three remaining plans.
No statement or definition changed.

## Proved and sorry left

Namespace: `AlgebraicGeometry.VectorBundleZeroSection`.
Closed 3 of the original 6 holes: `augmentation_spec`, `zero_spec`,
`affineChart_naturality`. Added 0 holes; split off 0 statements.

The 3 remaining holes are `affineChart_spec`, `trivializationMap_spec`, and
`transition_spec`, all attached to `def-asd-vector-bundle-zero-section`.
Their complete original statements and proof docstrings are retained.
The chart still needs the section-ring augmentation compatibility and efficient
elaboration of the dependent equivalence transports; the frame
statement needs the local polynomial identification and its gluing; the
transition statement needs the matrix expansion of the two inverse frames
and its transport to coordinates. A scratch chart proof checks the isomorphism and base-projection clauses, but
the complete theorem still lacks the augmentation clause. No unfinished scratch
proof is included. The resumed attempt also proved a generic categorical
section-map transport helper in scratch, but its application did not validate
the complete chart theorem; that unused helper is not delivered.

The retained work was compared with current sources: only three proof bodies
and one proof-only import differ. All Lean lines are at most 100 characters.
The resumed dry run passed: commit `2ede5ca72c` compiled and passed preflight
with review class CODEX (node proof record changed); nothing was pushed by that dry run.

## No longer needed

Removed the unused proof import `Mathlib.LinearAlgebra.SymmetricAlgebra.Basis`.
The remaining unproved frame theorem still needs its polynomial identification
as a planned argument, so its DAG dependency is retained. No public imports,
project modules, or nodes were pruned. All public imports are retained for the
existing definitions and statement interface.

The closed-immersion proof no longer needs the affine quotient-kernel argument
in the original docstring: Mathlib's separated-section criterion applies because
the bundle projection is affine. This removes no project dependency: the same
relative-spectrum construction remains necessary for the definitions and the
remaining chart statements.

## Where the brief, the DAG or earlier work was wrong

The node was a definition with an empty proof record; its Lean module contains
six substantive theorem obligations. The delivery records the actual three
completed arguments and the remaining plans. The original geometric proof
of the closed immersion can be replaced by the existing separated-section API.
The unit's construction and route, all signatures, and all definitions are preserved.
The earlier sandbox work survived its provider failure and was checked against
current sources. No independent second reading is claimed.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
