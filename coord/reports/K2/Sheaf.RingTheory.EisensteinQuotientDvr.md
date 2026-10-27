## What changed

Proved `IsDiscreteValuationRing.adjoinRoot_of_monic_eisenstein` in
`lean/Sheaf/RingTheory/EisensteinQuotientDvr.lean`, with its signature and public imports
unchanged. Mathlib Eisenstein irreducibility makes the quotient a domain directly.
The remaining argument constructs evaluation at zero into the residue field, identifies
its kernel with the root ideal, and proves this ideal is the unique maximal ideal by
integral contraction and the weak Eisenstein root-power lemma. The nonzero-root criterion
then gives the DVR structure. Updated the item's DAG proof and proof dependencies.

The proof follows Stacks 09ER (the final assertion, more-algebra.tex lines 34500–34514),
expanded by the standard Eisenstein criterion and the Noetherian local-domain criterion
in Stacks 00PD (algebra.tex lines 29104–29118). The proved binomial case in
`WeilConjectures.AlgebraicGeometry.Morphisms.DvrUniformizerRootAlgebra` supplied a useful
existing pattern for the residue-quotient and uniqueness arguments; it is not imported.

Validation: the reduced-import proof compiled through `lcompile.py` in 3.2 seconds.
`#print axioms` reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
The temporary axiom-print command was removed before delivery.

## Proved and sorry left

Closed the one existing hole:
`IsDiscreteValuationRing.adjoinRoot_of_monic_eisenstein`
(node `lem-sfb-eisenstein-quotient-dvr`). No holes added, no split-off statements,
and zero `sorry` declarations remain in the delivered Lean file.

## No longer needed

`lem-weil-pbc-dvr-unit-times-uniformizer-power` is no longer a proof dependency.
Mathlib Eisenstein irreducibility replaces the original Step 4 argument using
intersections of ideal powers and unit-times-uniformizer factorization.
No existing library declaration or module is withdrawn.

The proof no longer directly imports `Mathlib.RingTheory.Polynomial.RationalRoot`;
it imports `Mathlib.RingTheory.Polynomial.Eisenstein.Basic` instead.
The explicit `Mathlib.RingTheory.PrincipalIdealDomain`,
`Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, and
`Mathlib.RingTheory.Noetherian.Basic` imports are redundant through the remaining imports
and are removed. The underlying PID, integral, and Noetherian facts are still used.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original DAG's intersection-of-powers proof is
unnecessary because the existing Mathlib Eisenstein criterion already proves domainhood.
The proof directly applies `Polynomial.IsEisensteinAt.irreducible` and
`AdjoinRoot.isDomain_of_prime` from Mathlib; it does not cite the historical dropped
Eisenstein-criterion or polynomial-UFD DAG nodes or restore their former proof branches.
The unit statement and its route are unchanged. The proof covers degree one and arbitrary
residue characteristic, with no separability or completeness assumption.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
