## What changed

Completed the two proofs in `Sheaf.RingTheory.ParameterRootBoundaryDvrs`. All existing
public signatures, definitions, and public imports are unchanged. Added proved private
helpers for parameter permutations and quotients, the explicit surviving-variable
presentation, its monomial basis, contraction and unique primes, localization comparison,
and the fraction-field square. Proof-only imports provide root regularity, henselian
quotients, unique-prime localization, and the Mathlib APIs used by these constructions.

Updated `lem-sfb-parameter-root-boundary-dvrs` to describe the actual route. The basis is
transported from root regularity over the henselian parameter quotient. The localization
comparison uses integral incomparability and the existing unique-prime localization
theorem. Height one follows directly from Mathlib's principal ideal theorem. No source
library files or consumers were changed. The unit route is preserved.

## Proved and sorry left

Closed both original holes:

- `Algebra.parameter_root_boundary_quotients`.
- `Algebra.parameter_root_boundary_dvrs`.

The item contains zero `sorry`; zero holes were added and zero statements were split off.
All private helpers have complete proofs. These are proofs from existing project
statements, including `Algebra.henselian_parameter_root_regularity` and
`IsLocalization.uniquePrimeLocalization`, whose own unfinished proofs remain their
existing items. This delivery does not claim those dependencies are proved.

The argument covers an empty boundary by `Fin.elim0` and the empty-product prime
criterion; for one root the surviving monomial index has its constant monomial.
The root order is only assumed positive, including order one, throughout.

## No longer needed

Removed proof imports:

- `Mathlib.RingTheory.AdjoinRoot`.
- `Mathlib.LinearAlgebra.FiniteDimensional.Basic`.
- `Mathlib.RingTheory.DiscreteValuationRing.TFAE`.

Also removed imports introduced during development but absent from the final proof:
`Mathlib.Algebra.MvPolynomial.Rename`, `Mathlib.Algebra.BigOperators.Fin`, and
`Mathlib.RingTheory.Localization.Finiteness`.

This node no longer directly needs the following planned dependencies:

- `lem-weil-pbc-monic-quotient-free`: use the already-stated root-regularity basis
  over the henselian quotient and transport it through the explicit presentation.
- `lem-weil-pbc-finite-dimensional-domain-is-field`: the unique-prime localization
  theorem supplies the comparison without constructing a closed-fiber field here.
- `lem-weil-pbc-integral-maximal-contracts-maximal` and
  `lem-weil-pbc-local-ring-unit-criterion`: integral incomparability proves the unique
  prime, and the existing localization theorem supplies the rest.
- `lem-sc-dvr-dimension-one` and `lem-weil-pbc-primes-of-localization`: use
  `Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors` and
  `Ideal.eq_of_le_of_height_le` directly.

These removals concern this node's direct proof dependencies; dependencies still used
inside other imported results remain needed. No module or declaration is withdrawn.
The two existing `tool_uses` approvals are retained because both results are used.

## Where the brief, the DAG or earlier work was wrong

No statement repair was needed. The original eleven-step plan had unnecessary work
for this proof: the stated root-regularity theorem already provides the basis after
passing to the henselian parameter quotient, and the existing unique-prime localization
theorem applies after the short incomparability argument. The updated DAG records
these replacements and the additional existing dependencies. No new nodes were needed.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
