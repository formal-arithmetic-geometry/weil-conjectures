## What changed

Proved `Algebra.bertini_independent_functions` in
`Sheaf.AlgebraicGeometry.BertiniIndependentFunctions`, following the existing six-step
Stacks Tag 0G4E argument. The theorem's signature and all public imports are unchanged.

Constructed inverse ring maps between the special-fibre quotient and `A/(g₀,g₁)`;
transported the specified irreducible component and its dimension through the induced
homeomorphism; checked that evaluation defines a rational maximal ideal; applied
`Algebra.finiteType_fibre_component_lower_bound`; and contradicted a nonzero kernel using
Mathlib's quotient dimension-drop and polynomial-dimension theorems. Injective coefficient
and fraction-field maps then transfer algebraic independence to the stated field. The
coefficients are explicitly `c i = if i = ⟨1, hn⟩ then 1 else 0`.

Added proof imports for multivariate evaluation, the field dimension formula, the
nonzero-divisor dimension-drop API, spectrum ring maps, and tactics. No definitions, statements, other modules,
or DAG routes changed. No new nodes were required.

## Proved and sorry left

Closed the one original hole: `Algebra.bertini_independent_functions`
(node `lem-zl-bertini-independent-functions`). Added zero holes; zero `sorry`s remain in
the delivered module. The proof uses the existing stated fibre-component lower bound;
its own hole is unchanged and is not claimed as proved by this delivery.

## No longer needed

Removed the proof imports `Mathlib.RingTheory.Spectrum.Prime.Noetherian` and
`Mathlib.Topology.NoetherianSpace`: the argument needs Noetherianity of the algebra,
provided directly by `Algebra.FiniteType.isNoetherianRing`, rather than finiteness of its
spectrum's components. All existing declared proof-dependency nodes remain used; no
Sheaf or WeilConjectures module or node is pruned. The evaluation-kernel presentation
from `WeilConjectures.Mathlib.RingTheory.MvPolynomial.Ideal` was investigated but is not
needed or imported: the quotient construction uses the defining evaluation relations.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement error found. The quotient dimension-drop step is discharged
by Mathlib's `ringKrullDim_succ_le_of_surjective`, which implements the chain argument
already described in the node. The original unit route and target signatures are preserved.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
