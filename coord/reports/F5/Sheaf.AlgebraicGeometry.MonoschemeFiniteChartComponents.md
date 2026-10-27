## What changed

Proved `AlgebraicGeometry.Monoscheme.finite_chart_components` with its original signature.
The proof counts primes by subsets of finitely many monoid generators, transports this
finiteness through each atlas chart, and takes the finite connected-component quotient.
The empty monoid prime proves each affine open irreducible and connected. Basic opens
also distinguish prime carriers, yielding the ambient T0 property from the atlas.

The image of the empty prime of a chart generalizes the specified component generic
point, so it lies in every other chart of that component. Uniqueness in the existing
generic-point specification identifies these points. Thus the component fibre is the
closure of its generic point. The affine atlas makes the fibre open, and the closure
description makes it closed and irreducible. T0 gives uniqueness of maximal generalizations. Maximality of irreducible
components identifies the range of these fibres with all irreducible components.
All auxiliary declarations are private and completely proved.

Added private proof imports of `Sheaf.AlgebraicGeometry.MonoidPrimeMinimalNeighborhood`
and `Mathlib.Topology.Connected.Clopen`. Updated Steps 1--2 of the item's node to
describe the implemented proof. No new proof dependency is introduced in the DAG.
No unit statement or unit proof step is bypassed.

The empty atlas is handled by the surjection from its empty disjoint union. The trivial
monoid and an empty generating tuple are included in the finite-power-set argument.
No choice of an arbitrary algebraic object from an unproved existence statement is added.

## Proved and sorry left

Original holes: 4. Holes closed: 1, in
`AlgebraicGeometry.Monoscheme.finite_chart_components`
(node `lem-trf-monoscheme-finite-chart-components`). Holes added: 0. Split off: 0.

The three remaining holes are unchanged, all attached to the same item node:

- `AlgebraicGeometry.Monoscheme.finite_chart_components_algebra`;
- `AlgebraicGeometry.Monoscheme.finite_chart_components_localization`;
- `AlgebraicGeometry.Monoscheme.finite_chart_components_realization`.

This is a partial proof delivery, with one original hole closed and three retained.
The new proof uses the existing prime-face and generic-point obligations;
those are authorized dependencies rather than new holes in this packet.
Remote compilation checks the candidate and the delivery tool supplies the final
compile and preflight checks. No compiler options or time limits are changed.

## No longer needed

Removed unused private imports:

- `Mathlib.LinearAlgebra.FreeModule.PID`;
- `Mathlib.Algebra.AffineMonoid.UniqueSums`;
- `Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors`;
- `Mathlib.AlgebraicGeometry.ResidueField`.

These imports were not used by any proof in the delivered file. Their mathematical
inputs still belong to the documented plans of the three unchanged open theorems,
so no corresponding DAG dependency is withdrawn. No node, module, or adopted source
library declaration is pruned. All original public imports are preserved verbatim.

## Where the brief, the DAG or earlier work was wrong

No false statement or process defect was found. The first theorem's topology can be
proved directly from the prime-face statement and the existing unique generic-point
specification, so it needs no new decomposition statements.
The remaining three theorem plans are retained; this delivery makes no claim to have
proved their algebraic or gluing arguments.

## Second reading by F5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
