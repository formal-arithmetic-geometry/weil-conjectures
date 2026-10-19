## What changed

Proved `FrobeniusModule.spectrum_exact_sequence` in
`Sheaf.LinearAlgebra.SpectrumExactSequence`, preserving its exact signature and public imports.
Exactness identifies the image of the injection with the kernel of the surjection.
The injection and the first isomorphism theorem give equivariant linear equivalences with
this kernel and its quotient. Characteristic-polynomial invariance under these equivalences,
the existing invariant-subspace factorization, and `Polynomial.roots_mul` prove the assertion.
Updated the theorem docstring and the node's proof to describe this implementation.
The unit route and both declared dependencies are retained; no new statements or definitions.

## Proved and sorry left

Closed the sole original hole: `FrobeniusModule.spectrum_exact_sequence`
(node `lem-a1-spectrum-exact-sequence`). Proved 1 of 1 original sorries; added 0 holes;
0 sorries remain in the delivered module, and no statements were split off.
The proof uses the already proved characteristic-polynomial declarations from
`WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic` and Mathlib.
Remote single-file compilation passed in 2.4 seconds before final import cleanup.
The delivery checks compile the final version and report its axioms.
Zero-dimensional outer terms are covered by monicity and `roots_mul`; the proof assumes
neither semisimplicity nor a Frobenius-stable complement, and keeps all three carrier universes.

## No longer needed

No original imports, nodes, or modules are pruned. Both declared dependencies,
`def-weil-frobenius-module-weights` and `p-linear-filtration`, are used.
Removed the exploratory direct imports `Mathlib.Algebra.Exact.Basic` and
`Mathlib.LinearAlgebra.Isomorphisms`: both are already public transitive dependencies
of the retained characteristic-polynomial module.
The adapted-basis calculation is supplied by the existing proved filtration theorem.
No Laurent-polynomial or polynomial-reversal intermediate results are needed.

## Where the brief, the DAG or earlier work was wrong

The original node's second step described converting the determinant of `1 - t F`
to an ordinary characteristic polynomial using Laurent polynomials. The current
`blueprint_update` of `p-linear-filtration` and its existing Lean declaration already give
the ordinary characteristic-polynomial product directly. The updated proof uses that
actual declaration and retains the same mathematical route and dependencies.
No false or unusable statement was found, and no interface repair was needed.

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
