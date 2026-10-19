## What changed

Proved `AlgebraicGeometry.Scheme.completedAdic_levelwise_isomorphism_cones` with its
published signature unchanged. The proof represents a derived tower morphism by a
cochain map up to arrow isomorphism, uses Mathlib's levelwise quasi-isomorphism
criterion, and then applies the natural quotient reconstruction unit. It proves
both the zero-object criterion and the finite-reduction isomorphism criterion
without a separate cone argument. The existing node's proof and proof dependencies
now describe this route. No definitions or consumers changed.

The proof imports `Sheaf.Paper.KoszulReconstruction`. Its reconstruction comparison
and intrinsic-unit comparison are the existing stated dependencies intended for
this stage; no duplicate or new intermediate statement is introduced.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.completedAdic_levelwise_isomorphism_cones`
(node `lem-weil-pbc-levelwise-isomorphism-cones`).

Holes added: zero. Holes left in the delivered module: zero. This is a proof from
existing declarations, including the still-open reconstruction results in
`Sheaf.Paper.KoszulReconstruction`; it does not claim that those dependencies are
proved or that the theorem's transitive axiom closure is already sorry-free.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Homology.KFlatClosure`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Mathlib.CategoryTheory.Triangulated.Pretriangulated`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.Paper.CompletedRlimFunctor`
- `Sheaf.Paper.IntrinsicCompletionCompleted`

The three original public imports remain unchanged. Definitions and reconstruction
supply the needed coefficient API through their existing public imports.

The node no longer needs `def-weil-triangulated-category`,
`lem-sf-triangle-morphism-iso`, or `prop-weil-pbc-rlim-functoriality` as direct proof
dependencies: detection is by localization and levelwise quasi-isomorphisms, and
preservation of an isomorphism uses only functoriality. Removed the obsolete
`tool_uses` entries `lem-pc-kflat-resolution`, `lem-pc-kflat-cone-direct-sum`, and
`lem-pur-derived-change-of-rings`; there is no cone-tensor calculation here.
Some of these modules can remain transitive dependencies of the established
reconstruction API; no assertion is made that every target ceases to reach them.

## Where the brief, the DAG or earlier work was wrong

The old declaration docstring plans a longer cone-completeness proof. The current
blueprint node's natural reconstruction argument already avoids that detour.
Mathlib's levelwise quasi-isomorphism theorem also replaces the cone argument for
joint conservativity. This changes no unit statement or realized unit step.

## Second reading by S8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
