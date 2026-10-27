## What changed

Completed `Module.hilbert_affine_denominator_module` in
`Sheaf.RingTheory.HilbertAffineDenominatorModule`, preserving its signature and
all existing public imports. Added proof imports of
`Mathlib.RingTheory.Ideal.MinimalPrime.Localization`,
`Mathlib.RingTheory.Ideal.Colon`, and
`Mathlib.Algebra.Module.Submodule.Equiv`.

Constructed the denominator ideals as inverse images of ranges of multiplication
maps. Injectivity of the map to the total quotient ring identifies their
membership equations with the required fractional equations. The two existing
Mathlib leaves in the DAG establish regularity of a and b on M. Induction over
IM puts its a-multiple in the range of multiplication by b. The Mathlib inverse
onto that range constructs the unique linear division map. Cancellation proves
its injectivity, and explicit range witnesses prove both cokernel annihilators.
Updated the existing node's proof steps to describe these algebraic constructions;
its dependency set and source remain unchanged.

Read Stacks Divisors Tag 02P2, the affine proof through its final two annihilation
claims, and the current ample-degree unit. This realizes the same affine argument
and does not bypass any unit step. The map is constructed from an injective map's
inverse onto its range, whose values are uniquely determined; no arbitrary data
is obtained from an unproved existence theorem. No definition or statement changed.

## Proved and sorry left

Closed 1 of 1 holes: `Module.hilbert_affine_denominator_module`
(node `lem-sc-hilbert-affine-denominator-module`). Added 0 holes; split off 0.
No `sorry` remains in the delivered Lean module. Remote single-file compilation
passes without warnings. `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## No longer needed

None. No imports, nodes, or modules were removed. Both planned proof dependencies
are Mathlib leaves and are used. Explicit construction inside the localized module
is unnecessary: the equation `b • f z = a • z` and regularity of b uniquely specify
the same map, using Mathlib's inverse onto a linear map's range instead.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The full-support hypothesis is unnecessary once the
stated inclusion of associated primes in the minimal primes is assumed; it remains
in the unchanged theorem signature. The proof works for the zero module and the
zero ring as well, since it never assumes a or b is nonzero separately from their
regularity. No new lemmas, definitions, or nodes were needed.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
