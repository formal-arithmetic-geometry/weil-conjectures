## What changed

Proved `linear_incidence_irreducible` in
`Sheaf.AlgebraicGeometry.LinearIncidenceIrreducible`, preserving its statement and all
existing public imports. Added proof-only imports for polynomial division, polynomial
localization, and Krull height theorems. Fraction-ring declarations are already
available through the original public imports.

The five private helpers are fully proved. An invertible coefficient gives a polynomial
algebra automorphism taking a variable to the linear form, proving its primality.
Localization contraction identifies any minimal prime avoiding the denominators with
the contraction of that principal prime. The principal ideal theorem and the flat
height formula exclude minimal primes containing every coefficient. Evaluation at
zero then shows that every minimal prime contracts to zero in the coefficient ring.
Localizing at the fraction field identifies all minimal primes. The radical is prime,
so the quotient has prime nilradical and irreducible spectrum. Reducedness is not asserted.

Updated the item's DAG proof and dependencies to match these arguments. The additional
dependency `lem-weil-pbc-flat-height-formula` is an existing Mathlib leaf, used through
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`; polynomial flatness is inferred
from freeness. No new public statement, definition, node, or module is introduced.

The delivery gate requests a change record for `open MvPolynomial` and the local
registration of `MvPolynomial.algebraMvPolynomial`. The record is
`coord/changes/W4-linear-incidence-proof-commands.md`; it lists all 27 downstream
importers and explains why these local proof commands require no adaptations.

## Proved and sorry left

Closed hole: `linear_incidence_irreducible`
(node `lem-zl-linear-incidence-irreducible`), 1 of 1 original holes.
Added holes: none. Remaining holes in the delivery: none. Split off: 0.
All five private helpers are fully proved from Mathlib.

The earlier attempt's delivery probe typechecked the proof in 6.3 seconds and reported
`SHEAF-PROBED 1`. After resumption, an exact signature comparison again confirmed every
universe, binder, hypothesis and conclusion matches the current source. The unchanged
module compiled without warnings in 36.2 seconds. Following an intermittent delivery
compile timeout, a scratch copy with Lean's profiler enabled compiled in 8.9 seconds;
its aggregate type checking took 296 ms and typeclass inference 9.51 seconds. No
expensive definition required repair. The delivered source contains no profiling options.
The complete delivery preflight also checks the axiom probe.

## No longer needed

Removed the redundant candidate import `Mathlib.RingTheory.Localization.FractionRing`: it
is already available through the original imports. No original imports, nodes, or modules
are pruned. Every original declared dependency remains
relevant to the implemented argument. The direct Mathlib principal ideal theorem
supplies the principal-quotient height consequence. Explicit evaluation kernels,
coefficientwise denominator clearing, a manually extended chain of primes, and a
separate quotient-spectrum closed-set identification are replaced by Mathlib's
localization contraction, flat height, and nilradical criteria.

## Where the brief, the DAG or earlier work was wrong

No mathematical error in the statement or planned argument was found. Read the source
in Stacks `more-morphisms.tex`, Tag 0G4F, `lemma-bertini-irreducible`, lines 9089–9132.
The source's elimination and exclusion of vertical components are preserved; the
formal proof uses the equivalent prime-ideal argument in the DAG. The declared
polynomial-domain, Noetherianity, height, minimal-prime and spectrum dependencies are
Mathlib leaves, so no holed Sheaf dependency is necessary.

The proof covers the unit coefficient ideal (the height hypothesis is vacuous),
zero individual coefficients, and the single-variable case. Nonzero `hf` provides
a variable for the fraction-field argument; no additional hypothesis was introduced.
The unit-coefficient helper also works with a single variable, where the complementary
sum is empty. The height contradiction uses precisely `2 ≤ height`, excluding the
usual counterexample with a common height-one coefficient factor.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
