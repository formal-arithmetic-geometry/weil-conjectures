## What changed

Proved `WeilConjectures.IntegralImmersionNormalization.moduleRoundTrip_exists` in
`lean/Sheaf/Paper/IntegralImmersionPullbackNormalization.lean`. At each site object,
compose the inverse of Mathlib's scalar-restriction compositor with its identity
restriction comparison. The inverse identities of the completed coefficient ring
isomorphism give the required ring-homomorphism equality. These maps are identity
functions on sections, so they are natural in restrictions and module morphisms.
Extensionality on modules, site objects and sections proves uniqueness.

The original declarations, definitions, signatures, visibility and imports are unchanged.
The single-file server compile passed (11.7 seconds). No source-library file changed.

## Proved and sorry left

Closed 1 of the item's 2 original holes:
`WeilConjectures.IntegralImmersionNormalization.moduleRoundTrip_exists`.

The sole remaining hole is the unchanged named theorem
`WeilConjectures.IntegralImmersionNormalization.integralImmersionPullbackNormalization`,
attached to `lem-sf-integral-immersion-pullback-normalization`.
This is a partial delivery, not a proof of the main theorem. No holes were added,
and no statements were split off.

The retained main argument still requires assembling the published gamma and actual
completion unit with their specified shifts and scalar actions. Its geometric and
finite-quotient clauses were explored in the sandbox; no partial tactic proof is
included in the delivered theorem.

## No longer needed

None. No imports, nodes or modules are withdrawn. The existing main theorem and
its planned proof dependencies remain needed.

## Where the brief, the DAG or earlier work was wrong

No correction to a statement or definition is proposed. The completed coefficient
round trip is available directly from Mathlib's sectionwise restriction-of-scalars
isomorphisms; it requires no additional intermediate theorem or assumed data.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
