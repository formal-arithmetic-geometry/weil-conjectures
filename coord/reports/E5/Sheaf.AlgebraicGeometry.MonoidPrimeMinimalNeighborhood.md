## What changed

Filled `AlgebraicGeometry.FineFan.monoidPrime_minimal_neighborhood` in
`Sheaf.AlgebraicGeometry.MonoidPrimeMinimalNeighborhood` without changing its signature,
public imports, or definitions. The proof constructs the complementary submonoid and proves
all eleven conjuncts: the face and generator properties, both open-set intersections,
minimality, equality of localizations, the indexed inverse formula, and both unit criteria.
Closure induction gives face generation and denominator cofinality directly; induction on
the generated topology gives minimality. Updated the corresponding node proof to record
these elementary implementations. No other existing module is changed. The server single-file compile passed without warnings
in 4.9 seconds.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.FineFan.monoidPrime_minimal_neighborhood`
(node `lem-trf-monoid-prime-minimal-neighborhood`). Holes closed: 1. Holes added: 0.
No `sorry` remains in the item or is introduced elsewhere. No split-off statements.
The argument includes the empty index set, empty prime, and repeated generator values;
fineness is used for injectivity into the group completion in the unit criterion.

## No longer needed

None. Both original public imports are retained and used. The declared dependency
`def-trf-fine-fan-blowup` remains the only proof dependency. No nodes or modules are pruned.
No new proof imports are required. Closure induction replaces the explicit maximum-exponent
calculation within step 5, and generated-topology induction replaces the basis-neighborhood
argument within step 4; neither change bypasses a unit or removes a dependency.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement repair was needed. The inherited semigroup ideal is
exposed by Lean as `MonoidPrime.toSubMulAction`, because `SemigroupIdeal` is an abbreviation.
The original elementary proof plan is sufficient using the existing definitions and Mathlib.
The local delivery scanner interpreted the original docstring's line beginning
`axiom closes ...` as a forbidden declaration. Reflowed that sentence without changing
its text, so that the comment no longer starts a line with `axiom`.

## Second reading by E5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
