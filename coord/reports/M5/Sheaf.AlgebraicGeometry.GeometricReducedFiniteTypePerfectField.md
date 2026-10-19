## What changed

Proved `AlgebraicGeometry.geometricallyReduced_finiteType_of_perfectField` in
`Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField` without changing its signature.
The already proved library theorem `GeometricallyReduced.of_perfectField` supplies geometric
reducedness; Mathlib supplies flatness, local finite presentation and quasi-separatedness.
`pullback_of_geometrically` gives the exact field-extension pullbacks in the first clause.
Updated the node proof to the implementation; the existing theorem docstring is preserved.
The unit has no realized statement or steps at this node, and its route is preserved.

The module compiles through `lcompile.py`. An explicit `#print axioms` audit was also run.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.geometricallyReduced_finiteType_of_perfectField`
(node `lem-kun-geometric-reduced-perfect`). One of one holes proved; zero holes added,
zero split off, zero holes remaining in the delivered module. This is a proof, not a decomposition.

## No longer needed

Removed proof imports `Mathlib.AlgebraicGeometry.Fiber`,
`Mathlib.AlgebraicGeometry.PullbackCarrier`, `Mathlib.AlgebraicGeometry.Pullbacks`,
`Mathlib.RingTheory.FinitePresentation`, and
`WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced`.
Added the single proof import
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`;
kept `Mathlib.AlgebraicGeometry.Noetherian` for its instances and theorem.
The tensor-product and affine-pullback mathematics is reused through the existing library proof,
so its supporting nodes remain recorded as dependencies rather than falsely claimed pruned.

The old proof dependency `def-pc-scheme-fibre` is unnecessary: Mathlib defines geometric
reducedness directly by field-valued base change and supplies the bridge to the first clause.
No explicit residue-field identification, finite affine-cover construction, global Noetherianity,
or new scheme/fibre bridge module is needed. No whole project module is claimed globally unreachable;
public statement imports are preserved. The removed proof-import modules can remain transitively
reachable through the library theorem.

## Where the brief, the DAG or earlier work was wrong

Earlier searches missed the existing library theorem
`AlgebraicGeometry.GeometricallyReduced.of_perfectField`, proved in
`WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced`. It has precisely the required
hypotheses for geometric reducedness, even without finite type. The old eight-step proof is valid
but repeats that library argument and a residue-field comparison already covered by Mathlib's
geometric API. No statement, definition, consumer, or target repair is required.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
