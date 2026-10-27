## What changed

Proved `PrimeSpectrum.exists_basicOpen_image_subset_of_integral_field_algebra`
in `Sheaf.RingTheory.AlgebraicFieldImagePrincipalNeighbourhood`, with its signature
and public imports unchanged. The proof uses only Mathlib, with no auxiliary
public declarations. Updated the theorem's proof description and its DAG node to
match the implementation.

The basic-open cover gives a finitely supported unit relation. Its coefficients
and images generate a finite integral field subalgebra B. Finite prime avoidance
in the inverse-image subring S = phi^{-1}(B) supplies the required function.
Both inclusions follow directly by contraction and the ideal-span property.
The empty prime spectrum case is included explicitly; no nontriviality,
reducedness, domain, or finite-dimensionality hypothesis was added.

## Proved and sorry left

Closed 1 of 1 original holes:
`PrimeSpectrum.exists_basicOpen_image_subset_of_integral_field_algebra`
(node `lem-sfb-algebraic-field-image-principal-neighbourhood`).
Added 0 holes; split off 0 statements. No sorry remains in the delivered module.

Validation: lcompile.py compiled the proof cleanly (5.0 seconds). A temporary
`#print axioms` check returned exactly `propext`, `Classical.choice`, and
`Quot.sound`; the diagnostic command was then removed. The delivery preflight
also compiles the packet and checks its declarations.

## No longer needed

No imports, nodes, or modules are pruned: all six planned proof dependency nodes
are used through their Mathlib declarations. The explicit compactness substep is
replaced by finite support of ideal membership. The integer-generated subring
construction and the final conversion of prime avoidance to a unit are
unnecessary: the inverse-image subring and contraction of primes give the same
conclusion directly. These were elementary substeps, not separate DAG nodes.

## Where the brief, the DAG or earlier work was wrong

No false statement or unusable dependency was found. The original plan was valid;
the two simplifications above reduce the Lean bookkeeping while preserving the
finite-subalgebra and finite-prime-avoidance argument from Stacks Tag 0E21.

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
