## What changed

Proved `AlgebraicGeometry.nagata_sketch_closure` in
`Sheaf.Compactification.NagataSketchClosure` without changing its statement or docstring.
Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme` for the existing
scheme-theoretic dominance instance of `i.toImage`; `app_injective` then supplies density
on every open. The closed factorization uses `IsClosedImmersion.lift`,
`ker_le_ker_imageι_comp`, `toImage_lift`, `lift_fac`, and `eq_lift`.
For arbitrary dense opens, `ideal_ker_le` and injectivity on sections force the
quasi-coherent kernel ideal to vanish, so the existing separated-target extensionality
theorem applies without any quasi-compactness or reducedness assumption.

Scoped `linter.unusedVariables false` to this theorem: its existing nested forall names
`hj`, which is used by the proof but not by that binder's conclusion; its spelling and the
whole signature are preserved. No file-level option or public import changed.

The proof follows the node's three steps and all four stated dependencies. Read the
current main-20261015 unit statement and proof and Stacks morphisms.tex, labels
lemma-characterize-scheme-theoretically-dense, lemma-quasi-compact-immersion, and
lemma-equality-of-morphisms. Checked the edge cases of empty source, identity and closed
immersions, and a topologically dense but non-schematically-dense open in a nonreduced
scheme: the proof retains exactly the required sheaf-injectivity hypothesis.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.nagata_sketch_closure`
(node `sk-lem-nagata-sketch-closure`). Added 0 holes; 0 remain in the delivered module.
No split-offs or new declarations. The server single-file compiler accepted the final module cleanly in 3.0 seconds;
the delivery probe checks its axioms.

## No longer needed

None. No imports were removed, no modules or nodes were bypassed, and all four declared
proof dependencies remain used. Existing public imports are retained to preserve the
importer-visible interface. The added proof import is used by the density proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found in the assigned statement or its proof plan.
The unit JSON still describes the old master snapshot, with empty realized fields;
the current main-20261015 source and the assigned node agree, as the node's existing
split report records. No route or node change is needed.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
