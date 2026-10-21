## What changed

Simplified the private transposition proof in
Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMateUnit. The helper
mate_transpose_to now applies injectivity of the inverse Hom equivalence directly,
expands its formula, and uses conjugateEquiv_counit and naturality. Removed the
redundant private mate_transpose helper and the intermediate inverse-forward
calculation. The public theorem's statement, documentation and proof body are
verbatim unchanged. All imports, options and local attributes are unchanged.

Read both declared counit-normalization dependencies and their nodes. The main
proof still combines them by transposition and equality transitivity. The node's
proof already describes the direct private formal calculation, so its proof,
proof_deps and Lean attachment require no change. The unit route is preserved.

The unchanged baseline compiled through lcompile.py in 18.6 seconds. The revised
module also compiles through lcompile.py. Delivery runs the declaration and axiom
probes. No definition or public interface changes, consumer adaptations or change
records are needed. The existing consumer in
WeilConjectures.AlgebraicGeometry.DerivedDirectImageSquareMate uses the upstream
twin; no upstream file is changed. The retained Sheaf path and its DAG parent are
preserved.

## Proved and sorry left

The current assigned module already has zero direct sorries. The complete proof
of AlgebraicGeometry.derivedPullbackComposition_mate_unit
(lem-sc-derived-pullback-composition-mate-unit) is retained, with its private
transposition argument shortened. Holes closed: 0 of 0. Holes added: 0. Sorries
left in the item or added elsewhere: none. Split off: none. This is a proof
simplification, not a new hole closure or a decomposition.

## No longer needed

Removed the private helper AlgebraicGeometry.mate_transpose from this Sheaf
module: its only caller can prove the needed forward-Hom equation directly.
No import, DAG node or module is pruned. Both declared counit-normalization
dependencies remain used. No quarantined source is withdrawn or modified.

Loogle, LeanFinder and grep searches through msearch.py, together with source
searches, found Mathlib's generic conjugateEquiv_counit identity. Using it directly
removes the extra helper without changing the scheme-level route.

## Where the brief, the DAG or earlier work was wrong

The rework.tsv row still describes the quarantined restoration assignment, but
N4's restoration and redundant-attribute repair are already present in the shared
source and recorded as landed in
coord/changes/N4-derived-pullback-composition-mate-restoration.md. The baseline
compiles and has zero holes. There is no remaining definition repair identified
by that row, and this delivery does not claim to perform that already-landed
repair again. The present delivery makes a concrete private proof simplification.
No mathematical statement or dependency-plan error was found.

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
