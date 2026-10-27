## What changed

Proved `AlgebraicGeometry.affineGroupoid_invariant_norm` in
`Sheaf.AlgebraicGeometry.AffineGroupoidInvariantNorm`, preserving its full signature and docstring.
Four proved private helpers establish groupoid cancellation, the cartesian composition square,
affine norm base change, and its restriction formula for global sections. The proof then chooses
both charts from `hn`, refines their inverse images by an affine cover, compares the pulled-back
norms using the target-composition identity, and applies structure-sheaf separatedness.

The argument follows Stacks `groupoids.tex`, `lemma-diagram` and Tag 03BH
`lemma-determinant-trick`, read directly. The scalar-extension calculation uses the existing
Mathlib pushout-of-sections theorem, `Algebra.norm_eq_of_algEquiv`,
`Algebra.baseChange_lmul`, and `LinearMap.det_baseChange`. The existing norm-chart implementation
was read before writing the general base-change calculation. Search through LeanFinder,
Loogle and Mathlib grep found these ingredients but no groupoid norm-invariance theorem.

Replaced the public norm-chart-construction import by `Mathlib.RingTheory.Norm.Defs`, the
statement's actual norm dependency. Added only private proof imports for norm invariance and
determinant base change. The DAG proof now records the implemented argument and its dependencies.
No declaration, definition, target, or consumer statement changed. Both direct importers,
`AffineGroupoidOrbitFibres` and `AffineGroupoidPolynomialNormInvariant`, already import the norm
chart module themselves; no consumer adaptation is necessary.

## Proved and sorry left

Closed 1 of 1 holes: `AlgebraicGeometry.affineGroupoid_invariant_norm`
(node `lem-a1-affine-groupoid-invariant-norm`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. All four private helpers are proved.

Remote single-file compilation passed without warnings in 9.4 seconds after import cleanup.
`#print axioms AlgebraicGeometry.affineGroupoid_invariant_norm` reported exactly
`[propext, Classical.choice, Quot.sound]`; the diagnostic command was removed from the packet.
The proof handles empty spectra, zero-rank chart algebras, varying rank and nilpotents: no
nonemptiness, constant rank, domain or reducedness condition was introduced. It uses the
ordinary determinant base-change theorem, including its trivial-ring cases.

## No longer needed

Removed imports `WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts`,
`Mathlib.AlgebraicGeometry.Pullbacks`, `Mathlib.LinearAlgebra.Determinant`, and
`Mathlib.LinearAlgebra.Matrix.Determinant.Basic`. The latter three are already available through
necessary imports and require no separate import.

Removed proof dependencies `lem-pd-finite-locally-free-norm-charts` and
`def-weil-pbc-matrix-determinant`, and the former's obsolete `tool_uses` approval. The existing
`hn` already specifies the local norm; its existence theorem is not needed to prove invariance.
The norm-chart node stays a statement dependency because it describes that characterization.
Mathlib's determinant scalar-extension API replaces a manual Leibniz-formula calculation.
The affine fibre-product and endomorphism-determinant nodes remain, via the existing pushout
and determinant APIs. No module is withdrawn; the removed norm-chart module is still used by
other consumers, so no whole-library pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The planned argument is valid. The chart-existence
lemma is unnecessary in this proof since its conclusion is supplied by `hn`; the original
step 1's elementary label understated the cancellation and universal-property argument now
written in Lean. The current blueprint ancestor uses a newer coefficient route, but this
historical support lemma and its assigned mathematical statement are preserved. No unit route
is bypassed, and there are no new nodes or statement/definition changes.

The public-import change is recorded in
`coord/changes/affine-groupoid-invariant-norm-imports.md`, including every downstream consumer.
The first delivery preflight requested this record; it has been added to this packet.

## Second reading by U2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
