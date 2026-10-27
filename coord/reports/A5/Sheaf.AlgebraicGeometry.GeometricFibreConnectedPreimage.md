## What changed

Proved `AlgebraicGeometry.Scheme.Hom.isConnected_geometricFibre_preimage` in
`Sheaf.AlgebraicGeometry.GeometricFibreConnectedPreimage`, without changing its statement
or its public imports. Added a private proved helper
`subsingleton_pullback_of_unique_fibre` and the proof-only import
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Algebra`.
The helper uses the existing proved
`Algebra.IsUniversalHomeomorphism.of_isPurelyInseparable`, carried by
`lem-pc-spec-pure-insep-integral-radicial-surjective`.

The residue-field point covers all points of the indicated geometric fibre. Its
composite to the base is universally injective, so the geometric fibre has at most
one point. Mathlib's pullback point-surjectivity supplies a point. The open part of
the geometric fibre of T is therefore a singleton; applying
`Scheme.Hom.isConnected_preimage_singleton` to the base change of q finishes the proof.
Updated the item's DAG proof, dependencies and proof origin to describe this route.
No definition, statement, target or consumer interface changes.

Validation: the delivered module compiled successfully with `lcompile.py` in 2.1 seconds.
The existing public signature and public imports were compared with the source and agree.
The delivery preflight checks all introduced constants for axioms.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Hom.isConnected_geometricFibre_preimage`
(node `lem-weil-pbc-geometric-fibre-connected-preimage`).
Holes closed: 1. Holes added: 0. Sorries left in the delivered Lean: 0.
No split-off statements.

## No longer needed

The proof does not form the ordinary fibre or use `Scheme.Hom.fiberHomeo`:
`def-pc-scheme-fibre` is removed from proof dependencies. Its public import
`Mathlib.AlgebraicGeometry.Fiber` is preserved as part of the existing interface.
The separate algebraic-closure embedding argument is unnecessary: nonemptiness is
immediate from `Scheme.Pullback.exists_preimage_pullback`. Accordingly,
`def-weil-algebraic-closure`, `def-pc-field-extension`, and
`def-weil-pbc-finite-purely-inseparable-extension` are not separate proof dependencies;
these notions remain in the statement dependencies where originally present.
Pure inseparability is used through the residue-map predicate and the proved
source-library instance cited above. No modules are withdrawn; no imports are removed.
The route does not bypass any unit statement or realized proof step.

## Where the brief, the DAG or earlier work was wrong

No false statement found. The prior DAG proposed constructing an embedding into the
algebraic closure and identifying an iterated pullback homeomorphically with the
requested subset. Both are avoidable: pullback point-surjectivity proves nonemptiness,
and an equality with a singleton preimage under the base-changed q proves connectedness.
The private helper also covers an empty singleton base (its conclusion is only
subsingleton), and the main proof supplies nonemptiness explicitly. No additional
properness, finite type, affine, or residue-extension finiteness assumption is used.

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
