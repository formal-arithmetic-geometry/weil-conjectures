## What changed

Proved `WeilConjectures.IntegralSystemRealization.projectionRefinementSystems` by
specializing `properOpenProjectionMateSystems` to the square `(k, identity, a, i)`.
The commutativity proof is transported along `Category.id_comp i`. This proves the
intrinsic equality of system composites with the exact identity and compositor maps
already in the statement. It does not use detection by finite-level evaluation.

The finite-level theorem is unfinished. The attempted proof first transports K and L
to etale origins, reflects L's Tor interval, and uses the existing etale tensor and
pullback stability theorems to construct the tensor origin. The remaining local square
requires identifying the counit-defined comparison with the inverse of the specified
witnessed comparison, including the identity direct-image map and the direct-image
compositor. The site-level identities and generic categorical cancellations were
written, but their concrete coefficient specialization did not pass the single-file
compile limit. Those attempts are not included as unverified library declarations.

Successful isolated fragments used `finiteRing_constructibleDerived_origin`,
`intrinsic_hasProEtaleTorAmplitude_iff_torAmplitudeIn`, the etale Tor-pullback and
bounded-constructible tensor lemmas, and `comparisonOpenTensorIso` for domain preparation.
The natural comparison family was transported from `compactification_coherence` through
the fully faithful origin-forgetful functor, with normalization on every retained witness.
The common-refinement cancellation helper also compiled with raw complexes as inputs.
These isolated checks do not close the finite theorem: the full combination, including
its public `refinementLaw` and restricted source/target functors, was not validated.

Validation: the complete module with the system proof and the original finite theorem
compiled in 7.5 seconds. The delivered module preserves all original public statements,
definitions and imports. No source-library module or target statement is changed.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.IntegralSystemRealization.projectionRefinementSystems`.

One original hole remains:
`WeilConjectures.ProjectionRefinementDescent.finite_descent`, attached to
`lem-sf-projection-refinement-descent`, with its original full proof plan and source.

Added holes: zero. Split-off holes: zero. This is a partial proof delivery, with no
relocation of the unfinished finite-level theorem. The system proof uses the existing
named mate theorem; its transitive outstanding dependencies remain separate items.

## No longer needed

None. No imports, nodes, modules or declarations are withdrawn. The finite-level plan
still needs its recorded dependencies, so no pruning is claimed from an unsuccessful
alternative route.

## Where the brief, the DAG or earlier work was wrong

No false mathematical statement was found. A proposed shortcut through
`FixProjectionCompactification.comparison` is circular: the current proof route of its
finite comparison theorem depends on this item. It is therefore not used.

The concrete fixed-scalar coefficient types expose different definitionally equal
`Ring` dictionaries (`ULift.ring` and the `Ring` projection of `ULift.commRing`).
Converting large derived tensor and comparison expressions across these dictionaries
was expensive. The attempted normalization also required aligning generated sheafification
and Grothendieck-category proof instances. Generic category-theoretic versions compiled,
but this did not suffice to validate their concrete specialization. No definition repair
is claimed without a passing full compile. The blueprint unit's route is retained.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
