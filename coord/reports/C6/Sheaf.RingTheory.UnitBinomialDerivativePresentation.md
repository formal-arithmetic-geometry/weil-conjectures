## What changed

Filled `Polynomial.UnitBinomial.derivative_presentation` in
`Sheaf.RingTheory.UnitBinomialDerivativePresentation` with the planned explicit quotient
calculation. The root relation yields the inverse of the root; the given inverse of `n`
then yields the displayed inverse derivative. Evaluation at the root and that certificate
factors through the two-variable quotient, and evaluation at its first generator factors
through the binomial quotient. Polynomial extensionality proves the composites are identities;
the second generator is fixed by uniqueness of a multiplicative inverse.

All existing statements, definitions and public imports are preserved. The proof uses the
existing Mathlib leaves for polynomial evaluation, quotient algebra maps and extensionality.
It follows all six steps of the existing node without new dependencies or a route change.

Validation: the required server single-file compile passed in 4.7 seconds without warnings.

## Proved and sorry left

Closed the sole existing hole: `Polynomial.UnitBinomial.derivative_presentation`
(node `lem-sfb-unit-binomial-derivative-presentation`). Added zero holes; zero remain.
No statements were split off. The hypotheses and proof include `n = 1` and the zero ring.

## No longer needed

None. All three declared dependencies are Mathlib leaves used by this proof. No existing
imports, nodes or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. No statement or definition repairs were needed.

## Second reading by C6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
