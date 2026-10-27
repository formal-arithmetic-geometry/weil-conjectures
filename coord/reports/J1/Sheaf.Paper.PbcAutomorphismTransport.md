## What changed

Filled `AlgebraicGeometry.Scheme.pbcIsoAmbientScalarComparison_exists` in
`lean/Sheaf/Paper/PbcAutomorphismTransport.lean`. The proof adds private generic
right Kan extension helpers for transporting a normalized left derived counit
through exact equivalences, then specializes them to the completed scalar map and
the ordinary scalar comparison. The helper proves both the complex counit equation
and uniqueness. The existing preservation theorem remains unchanged with its
original `sorry`.

The module adds the proof-only import
`WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.LeftDerivedEquivalence`
and the derived-square infrastructure import
`Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares`. Local irreducibility
attributes keep the derived comparison within the 60-second file limit.

## Proved and sorry left

Closed one original hole:

- `AlgebraicGeometry.Scheme.pbcIsoAmbientScalarComparison_exists`.

One original `sorry` remains, with node `def-wf-automorphism-completed-transport`:

- `AlgebraicGeometry.Scheme.pbcIsoAmbientPullback_preserves`.

No holes were added and no definitions contain `sorry`.

## No longer needed

No modules or DAG nodes were pruned. The existing proof-dependency route remains
needed by the preservation theorem and by the completed and integral transport
constructions. The imported right Kan extension and derived-square declarations
are used by the private scalar-transport helpers.

## Where the brief, the DAG or earlier work was wrong

The DAG described the scalar comparison as an unfinished named theorem. Its
normalization can be proved directly from the exact-equivalence derived-square
construction already available in the library. The preservation clause still
requires the three geometric transport arguments described by its docstring and
was not weakened or replaced.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
