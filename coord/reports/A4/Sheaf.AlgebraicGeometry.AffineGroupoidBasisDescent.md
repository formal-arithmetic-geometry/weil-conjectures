## What changed

Proved `AlgebraicGeometry.affineGroupoid_basis_descent` in
`Sheaf.AlgebraicGeometry.AffineGroupoidBasisDescent`, preserving its statement.
The proof imports and follows exactly the three existing dependencies in the current DAG:
`AlgebraicGeometry.affineGroupoid_coordinate_identities`,
`RingHom.twistedTensor_invariant_coefficients`, and
`RingHom.invariantCoefficients_reconstruction`.

The coordinate identities provide the common retraction and the composition coordinate map.
The two explicit twisted tensor-product presentations are definitionally equal, so the
composition identities apply directly to the invariant-coefficient theorem. The proof reverses
expansion equalities to match reconstruction's convention, then extracts its basis and ring
equivalence. No definitions, signatures, public imports, other existing modules, or DAG routes
changed. The existing node already records this exact three-step argument.

LeanFinder, Loogle, and local source searches found no shorter existing theorem; the stated
three-step route needs no additional lemma. Single-file compilation passed in 3.2 seconds.

## Proved and sorry left

Closed one hole: `AlgebraicGeometry.affineGroupoid_basis_descent`
(node `lem-a1-affine-groupoid-basis-descent`).

Zero holes remain in the item module; zero holes were added or split off.
The proof uses the three already stated dependency theorems above, whose existing holes remain
in their own modules. This delivers the requested proof from those declarations, rather than
an axiom-free completion of their downstream mathematics.

## No longer needed

Removed the unused private imports `Mathlib.LinearAlgebra.TensorProduct.Basis` and
`Mathlib.RingTheory.TensorProduct.Maps` from the item module.
All three declared proof dependencies are used; no DAG node or project module is pruned.

## Where the brief, the DAG or earlier work was wrong

No correction was required. The declaration's older six-step docstring and the current
three-step DAG describe the same argument, with the current DAG grouping the algebraic steps
into the three existing dependency theorems. No change record or new node is needed.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
