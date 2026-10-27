## What changed

Proved `AlgebraicGeometry.Scheme.adicExactComparison` in
`Sheaf.Paper.AdicExactComparison`, preserving its exact statement and both public imports.
Added the proved private helper `ordinaryComparison`.

The proof uses the existing constant-inverse-image scalar normalization, the
continuous ringed-topos construction, and the proved `supplied_module_adjunction`
helper imported privately from `CompletedPullbackAdjunction`. Both ordinary
functors are left adjoint to the identical module pushforward. Uniqueness of left
adjoints gives their natural isomorphism. Exactness transfers across it, and
Mathlib's theorem on an already exact left-derived functor makes the universal
adic comparison counit invertible. The termwise ordinary comparison finishes.
The completed-pullback theorem itself is not invoked.

Added only private proof imports of
`ConstantInverseImageScalarNormalization`,
`ContinuousRingedToposModuleDirectImage`, `CompletedPullbackAdjunction`,
`ConstructibleComparisonModuleExact`, and Mathlib's `PointwiseLeftDerived`.
Updated the item's DAG proof, dependencies, and proof origin to this argument.
No definitions, public signatures, instances, or other existing modules changed.

The server compiled the complete file without diagnostics in 8.6 seconds.
LeanFinder, Loogle, and Mathlib grep searches through msearch located the exact
localization and left-derived-functor APIs; repository searches located the
already proved scalar normalization. The argument has no nonempty-site,
nonzero-ring, Noetherian, boundedness, or constructibility hypothesis, so it
also applies to the empty scheme and zero coefficient ring.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.adicExactComparison`
(node `lem-sfb-adic-exact-comparison`).

Added 0 holes and split off 0 statements. No `sorry` remains in the item or is
added elsewhere. `ordinaryComparison` is a fully proved private helper.
Existing imported statements retain their existing proof dependencies.

## No longer needed

Removed the proof dependency `lem-pe-coefficient-comparison-derived-functor`
(module `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonDerivedFunctor`).
Its derived localization and cohomology comparisons are unnecessary here:
exactness and the existing universal adic counit suffice directly. This is a
local dependency pruning; other consumers may still require that module.

No existing import was removed: both original public imports occur in the
statement. Every added proof import supplies a used declaration. The original
ordinary module-adjunction and geometric-construction dependencies remain,
realized by the proved generic helper rather than restated or split off.
The blueprint unit statement and all its steps remain intact.

## Where the brief, the DAG or earlier work was wrong

The existing plan is valid. Its final step can be shortened: no separately
constructed exact derived comparison functor is necessary. Mathlib directly
proves that the comparison counit of a left-derived functor is invertible when
the original functor already inverts the localization class. The needed
constant-ring normalization was already proved elsewhere in the library, so
no further decomposition was needed.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
