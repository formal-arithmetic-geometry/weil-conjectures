## What changed

Proved `AlgebraicGeometry.smooth_connected_fibre_normal_integrality` in
`Sheaf.AlgebraicGeometry.SmoothConnectedFibreNormalIntegrality` with its signature unchanged.
The proof applies the prescribed, already proved
`Scheme.smooth_connected_generic_geometry_core` to the displayed fibre base change over
`Spec K`. Mathlib supplies both smooth base changes and geometric connectedness after
pullback; connectedness over the one-point field spectrum supplies nonemptiness.
`Scheme.isIntegrallyClosed_stalk_Spec` supplies normality of the field base, and the
integral-scheme stalk instance supplies the domain conclusion.

Updated the item's node proof and proof dependencies to describe this assembly.
Added a private proof import of `WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme`.
The import change is recorded in
`coord/changes/smooth-connected-fibre-normal-integrality-imports.md`.

Validation: the final module compiled without errors or warnings through `lcompile.py`
in 2.8 seconds. There are zero direct Lean importers requiring compatibility compiles.
The statement includes arbitrary, possibly inseparable or transcendental K; no extra
finiteness or normality hypotheses are introduced. Empty B is vacuous and empty fibres
are excluded by geometric connectedness, as in the original statement.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.smooth_connected_fibre_normal_integrality`
(node `lem-trf-smooth-connected-fibre-normal-integrality`).

Sorries left in the item: none. Holes added: zero. Split-off statements: zero.

## No longer needed

Removed private import `Mathlib.AlgebraicGeometry.Morphisms.Proper`: smooth base change
is supplied by `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, which remains imported.
The dependency `lem-pc-proper-base-change` remains for its smoothness clause.

Removed public import `Mathlib.AlgebraicGeometry.Geometrically.Integral`: neither the
statement nor the proof uses `GeometricallyIntegral`. The node
`def-pc-geometrically-irreducible` is no longer a separate proof dependency; the
`GeometricallyConnected` statement dependency and import remain.

Replaced public import `WeilConjectures.AlgebraicGeometry.BaseChangeConventions` with
`Mathlib.AlgebraicGeometry.Fiber`: only the actual fibre and pullback definitions are
needed. `def-pc-base-change` is no longer a separate proof dependency. The statement
still refers to that convention, and no DAG node or source declaration is withdrawn.

No other nodes or modules are pruned by this delivery. In particular the prescribed
generic geometry core and the unit route are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The smooth connected generic geometry core is
already fully proved in the current source library, so the entire item is an assembly
of existing declarations. Its recorded module is under
`WeilConjectures.AlgebraicGeometry.Morphisms`, as used by the original private import.
The final proof uses the general pullback-connectedness instance to package the
node's elementary field-extension/pasting argument.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
