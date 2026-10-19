## What changed

Proved `RingTheory.isOpen_regularLocus_of_primeQuotient_regularOpen` without changing its
statement or public imports. Private proved helpers implement generalization stability,
parameter numerators, denominator clearing, localization of the regular sequence,
quotient localization, and the principal neighbourhood inside each closed subset.
Nagata's existing criterion then gives an open neighbourhood at every regular prime.

The construction follows Stacks 07P9. It clears denominators directly at each prime
avoiding the chosen product, avoiding an intermediate identification of two successive
principal localizations. The nonempty open in the quotient is refined directly using
the basis of principal opens. No definitions or existing public signatures changed.

## Proved and sorry left

Closed the one original hole:
`RingTheory.isOpen_regularLocus_of_primeQuotient_regularOpen`
(node `lem-exc-regular-locus-open-from-prime-quotients`).

No holes remain in the delivered module; no holes or modules are added. All private
helpers are proved. This proof uses the existing declared results on regular local
localizations, regular systems of parameters, spreading regular sequences, and lifting
regularity from a regular-sequence quotient; their transitive holes remain their own items.
The unused, undelivered scratch module `RegularLocusNagataHypotheses` from the earlier
attempt was removed from the sandbox, rather than introducing a redundant new hole.

## No longer needed

Removed proof-only imports `Mathlib.Algebra.Module.LocalizedModule.Exact` and
`Sheaf.AlgebraicGeometry.IsRegularScheme`. The proof uses the preservation theorem in
`Mathlib.RingTheory.Regular.Flat` and the regular-parameter API directly.

The route no longer directly needs `lem-weil-pbc-localization-quotient-commute` (prefix
quotients are handled by the existing preservation theorem),
`lem-weil-pbc-spec-irreducible-closed-subsets-primes` (the basic-open basis suffices), or
`lem-weil-pbc-weakly-regular-sequence-localization-prime` (apply weak regularity under
localization and the local maximal-ideal criterion directly). No library module is
withdrawn. The item's node records the actual seven-step proof. The unit route is retained.

## Where the brief, the DAG or earlier work was wrong

The retained attempt contained two failing helper proofs and an unfinished final proof,
plus an unused scratch theorem bundling both Nagata hypotheses. Those issues are repaired
without delivering any new theorem with `sorry`. The DAG's longer localization argument
is valid but unnecessary: denominators can be cleared in the eventual prime localization.
No mathematical statement was disputed or changed.

On resumption, the first successful compile and axiom probe passed. Preflight then detected
an extra module-level universe command in the retained proof. Restricted the private
unit-scaling helper's index type to `Type` (its only application uses `Fin d`) and restored
the original `universe u` command, preserving the module's public interface.

## Second reading by Q8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
