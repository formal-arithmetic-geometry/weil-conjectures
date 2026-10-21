## What changed

Restored `lean/Sheaf/AlgebraicGeometry/TensorSinglePullbackComposition.lean`
from its quarantine archive. The current rework assignment records its removal
after a cluster restore; the library path was absent. This is a restoration of
the four public declarations and their complete proofs, not a withdrawal or a
new formulation of the coefficient comparison.

The restored source is byte-for-byte identical to the archive. Its public
imports already refer to the adopted source implementations of
`SchemeDerivedMateEvaluation` and `TensorCoefficientComparison`, and its private
ordinary-composition import already refers to the adopted source implementation.
The recently restored canonical single-pullback composition prerequisite now
provides the remaining proof import. No declaration, definition body, universe,
hypothesis, public import, or proof route changed from the archived version.

The main theorem uses the proved ordinary coefficient composition identity,
naturality of the canonical single comparison, and
`canonicalSinglePullbackComposition`. The naturality proof pastes naturality
of the selected derived counit, the termwise single-complex comparison, and
the unique tensor-to-ordinary adjunction comparison. Private generic category
calculations handle reassociation. Substitution of `a' = b ≫ a` removes the
equality transport, and the single functor maps the ordinary coefficient
identity. The wrapper composition theorem unfolds the explicit coefficient
morphism and applies this theorem. The single comparison is never inverted,
and no flatness or invertibility hypothesis is introduced.

The compatibility record is
`coord/changes/H2-tensor-single-pullback-restoration.md`.

## Proved and sorry left

This is a zero-hole rework assignment. The archived module has zero `sorry`s;
zero original holes were closed, zero holes were added, and zero were split off.
The restored public declarations are:

- `AlgebraicGeometry.tensorSingleCoefficientMap`;
- `AlgebraicGeometry.tensorSingleCoefficientMap_eq`;
- `AlgebraicGeometry.tensorSinglePullback_composition`;
- `AlgebraicGeometry.tensorSingleCoefficientMap_composition`.

The definition is the explicit composite prescribed by
`def-sc-tensor-single-coefficient-map`. Both composition theorems and all four
private helpers have complete proofs. There is no remaining hole in the item.
The first clean single-file compile took 24.7 seconds under the unchanged
60-second limit.

A scratch copy with `#print axioms` for all four public declarations and all
four private helpers compiled cleanly in 38.1 seconds. Every axiom list is a
subset of `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs
in their transitive proof dependencies.

An import-ordered sandbox check compiled the restored module in 40.8 seconds
and the unchanged quarantined direct importer
`Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting` in 20.4 seconds,
both without warnings or errors. The consumer used the actual compiled output
of the restored module. The source and all public declaration bodies remain
identical to the quarantine archive.

## No longer needed

None. All five imports remain used by the existing signatures, definition, or
proofs. Every dependency of `lem-sc-tensor-single-pullback-composition` remains
needed. The unit `sk-prop-av-cube` and both existing item node attachments are
preserved. The quarantined parent
`Sheaf.AlgebraicGeometry.PicardCoefficientTransposePasting` still cites the item
in its DAG proof and imports it in Lean; zero current live importers therefore
does not justify withdrawing it. No module or node was pruned, and no new node
was introduced.

## Where the brief, the DAG or earlier work was wrong

The current rework row correctly identifies a cluster-restore regression.
The archived mathematics and proof route need no repair: restoring the missing
library file against the current prerequisites restores the implementation.
The historical K3 report's one-hole proof count is not this assignment's count;
that proof was already present in the archive.

The first compile reported that the recently landed prerequisite
`Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComposition` had no
published object file. Diagnostic sandbox copies were not part of the
restoration. Once that object was published, the unchanged assigned module
compiled cleanly against the shared library. No prerequisite edit is delivered.

LeanFinder and Loogle searches found the generic pullback and naturality
ingredients; the Mathlib source search found `singleMapHomologicalComplex`
and the homotopy single-functor implementation. No public replacement for this
fixed tensor coefficient composition was found. The existing declared
dependencies give the complete argument, so no further split is needed.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
