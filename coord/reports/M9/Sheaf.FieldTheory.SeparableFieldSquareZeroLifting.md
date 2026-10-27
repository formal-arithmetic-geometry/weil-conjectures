## What changed

Filled `Algebra.exists_lift_of_isSeparableExtension` in
`Sheaf.FieldTheory.SeparableFieldSquareZeroLifting`, with its signature unchanged.
The proof follows all four existing DAG steps: separably generated intermediate
fields are formally smooth by Mathlib; their first cotangent homology vanishes;
`Algebra.subsingleton_h1Cotangent_of_finite_subfields` passes vanishing to the
whole extension; vector-space projectivity gives formal smoothness of the whole
extension and `Algebra.FormallySmooth.comp_surjective` supplies the lift.
The range of the separating set's subtype inclusion is identified with that set
before installing the separable algebraic extension instance.

The proof uses precisely the existing dependency declarations. No new theorem,
node, definition, statement change, or change to a shared module is required.
The existing node proof and proof dependencies already describe this route.

## Proved and sorry left

Closed the one hole in `Algebra.exists_lift_of_isSeparableExtension`
(node `lem-sfb-separable-field-square-zero-lifting`). No holes remain in the
item, and no holes were added or split off. The final single-file server compile
passed without warnings in 2.4 seconds.

## No longer needed

Removed redundant private imports `Mathlib.RingTheory.Kaehler.Basic`,
`Mathlib.Algebra.Module.Projective`, and
`Mathlib.LinearAlgebra.Basis.VectorSpace`: all three are publicly reachable
through the retained proof import `Mathlib.RingTheory.Smooth.Field`.
Their differential, freeness, and projectivity declarations remain used.
No mathematical dependency node or module is pruned: all seven declared
proof dependencies are used, and the existing unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. LeanFinder's remote index reports an
extra essential-finite-type assumption on the separably generated formal
smoothness lemma; the checked local Mathlib signature has no such assumption.
The proof uses that local signature and imposes no finiteness or characteristic
restriction on the whole extension. Edge cases (the bottom intermediate field,
zero square-zero ideal, and arbitrary transcendence degree) require no separate
hypothesis or argument.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
