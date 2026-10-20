## What changed

Proved `CategoryTheory.boundedFilteredComplex_pageFunctor_normalized` in
`Sheaf.CategoryTheory.BoundedFilteredPageFunctorNormalized`, preserving its statement
and both public imports verbatim. All ten planned steps are implemented.

The concrete quotient pages carry the uniquely specified representative differential.
The canonical page maps and the uniquely normalized successor isomorphisms assemble
into one spectral-sequence functor. The successor-cycle cover and uniqueness give
both directions of the normalization equivalence. The successor naturality equation
is the compatibility equation of that same functor.

The proved private helper `normalizedPage_comparisons` repeats the proof of
`filteredQuotient_comparisons_rest`, retaining its general-page representative equation
in the conclusion. It reuses the existing private representative-comparison and
naturality helpers through a proof-only `import all`. This supplies first-page and
image comparisons compatible with the identity quotient comparisons, including the
required representative equation. No dependency interface or definition is changed.
The exact-couple and abutment data come from the stated declarations. The existing
private page-core stabilization helpers apply to this same functor, so no finite
bound on the cochain degrees is introduced.

Updated the item's DAG proof to record the retained representative equation and the
reuse of the page-core stabilization helpers, adding the directly used boundary
containment and page-core nodes to proof dependencies. The unit route is unchanged;
the unit record has no realized statement or proof-step node that this argument bypasses.

Validation: the final proof compiled without warnings through `lcompile.py` in 8.6 s.
`#print axioms CategoryTheory.boundedFilteredComplex_pageFunctor_normalized` reported
exactly `propext`, `Classical.choice`, and `Quot.sound`; there is no transitive sorry.
The theorem's entire signature was compared with the shared source and is unchanged.
Every Lean line is at most 100 characters.

The dry run passed compilation and server preflight. Later verification attempts
intermittently hit the 60-second limit. Profiling the unchanged full proof compiled
in 31.7 s; profiling it with the exact delivery probe compiled in 22.9 s. Finally,
the unchanged, unprofiled proof with that probe compiled without warnings in 20.0 s
and printed `SHEAF-PROBED 1`, with no axiom or sorry findings. No definition exhibited
runaway unfolding. A sequential-elaboration experiment did not improve timings and
was discarded. All diagnostic variants were confined to a scratch copy. No
compilation limit, linter or proof check was disabled, and the delivered proof
keeps its original elaboration settings.

## Proved and sorry left

Closed 1 of 1 original holes:
`CategoryTheory.boundedFilteredComplex_pageFunctor_normalized`
(node `lem-kun-filtered-page-functor-normalized`).

Remaining holes: none. Added holes: zero. Split-off statements: zero.
The private helper is fully proved, and the public theorem has only the three permitted axioms.

## No longer needed

Removed redundant direct proof imports:

- `Sheaf.Algebra.Homology.FilteredComplexQuotientImageComparison`;
- `Sheaf.Algebra.Homology.FilteredComplexRepresentativeEpis`;
- `WeilConjectures.Algebra.Homology.FilteredComplexSubquotients`;
- `WeilConjectures.CategoryTheory.Abelian.Filtration`.

Their mathematical results remain needed through the retained comparison helpers or
public statement imports. No node, declaration, or module is withdrawn or pruned
from the targets' dependency closure. The original public imports remain unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The existing comparison and canonical-functor proofs
already construct normalized witnesses, but their public existential conclusions do
not retain all the equations required here. Applying those theorems alone would lose
the compatibility between the globally chosen quotient comparisons and the image
representative equation. The private helper retains that equation, and the functor
is assembled explicitly from the already proved normalized homology and naturality
theorems. No new mathematical result or unproved intermediary was needed.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
