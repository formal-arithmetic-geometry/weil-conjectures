## What changed

Proved `RingTheory.coprimeGeneratorsMprimaryOrUnit` in
`Sheaf.TraceFormula.CoprimeGeneratorsMprimaryOrUnit` without changing its statement.
A minimal finite generating set of the maximal ideal supplies a regular parameter
list. Applying `regularLocalUFDBoundaryFactorization` with an empty selection
supplies the UFD instance. The generated ideal is nonzero, since otherwise zero
would be a common divisor and hence a unit. Every prime containing the ideal is
maximal: a strictly smaller prime has height at most one because the maximal
ideal has height two, and nonzeroness forces height exactly one. Mathlib's
`UniqueFactorizationMonoid.isPrincipal_of_height_eq_one` makes that prime
principal; the common-divisor hypothesis makes its generator a unit, a
contradiction. `Ideal.radical_eq_sInf` then identifies the radical.

Added the private proof import `Mathlib.RingTheory.Ideal.UFD`. The existing DAG
argument and all its dependencies are retained, including the empty-selection
application of the regular-local UFD theorem. No DAG or interface change is
necessary. The source paragraph in Stacks `curves.tex`, Tag 0C48, and the current
blueprint unit `sk-i-curve-zero` were read; the unit route is unchanged.

## Proved and sorry left

Closed the one existing hole:
`RingTheory.coprimeGeneratorsMprimaryOrUnit`
(node `lem-trf-coprime-generators-mprimary-or-unit`).

Holes closed: 1 of 1. Holes added: 0. Split off: 0.
No `sorry` remains in the item module. All imported project declarations used
here already exist; no dependency declaration was changed. Server compilation succeeded without
warnings (6.0 seconds). `#print axioms` reported exactly `propext`,
`Classical.choice`, and `Quot.sound`; the temporary diagnostic command was
removed after this check.

## No longer needed

Removed the private proof import `Sheaf.AlgebraicGeometry.IsRegularScheme`:
this proof concerns the ring predicate `IsRegularLocalRing`, already supplied
by the existing public Mathlib import, and does not use the scheme definition.
The ring clause of `def-weil-regular-scheme` remains relevant; no DAG dependency
is pruned. No other node or module is withdrawn. All original public imports
are preserved.

## Where the brief, the DAG or earlier work was wrong

None. The Lean proof realizes the stated four-step plan using the available
Mathlib height API for the dimension-two prime-chain argument and the radical
intersection formula for the last step. The empty family and all-zero family
are excluded directly by applying the common-divisor hypothesis to zero;
no positivity assumption on the number of generators is added.

## Second reading by M8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
