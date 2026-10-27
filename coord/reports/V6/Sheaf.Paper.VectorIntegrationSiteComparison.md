## What changed

Proved `AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorIntegrationSiteComparison`
in `Sheaf.Paper.VectorIntegrationSiteComparison`, keeping its full Noetherian-base
statement. Added the proof-only import `Sheaf.Paper.OrderedIntegrationComparison`.
Three proved private calculations identify the pulled-back constant unit, the local
frame trace, and comparison of an ordinary normalized integration. Uniqueness of
`existsUniqueVectorIntegration` identifies the actual chosen global integration;
cancellation of the canonical source comparison gives the required map equation.
The DAG proof records this route. No public signatures, definitions, target
statements, instances, or public imports change.

## Proved and sorry left

Closed one of the four original holes:
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorIntegrationSiteComparison`.
Added zero holes and split off zero statements.

Three original holes remain, all attached to
`lem-pur-vector-integration-site-comparison`:

- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.projectiveComparison`.
- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorTensorComparison`.
- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorExponentIndependence`.

The existing proofs of `openCounitComparison`, `twistCompatibility`, and
`finiteTypeSiteComparison` are preserved. The latter now uses the completed
integration-comparison clause.

Validation: single-file compilation through `lcompile.py` and delivery preflight.
The result is a proof from existing declarations, including their recorded open
proof dependencies; it does not claim their transitive axioms have all been closed.

## No longer needed

No existing import is removed. For the completed global-integration clause, the
separate finite-type affine-tower and frame-descent route is unnecessary:
`lem-pur-affine-tower-integration-site-transport`
(`Sheaf.Paper.AffineTowerIntegrationSiteTransport`),
`lem-pur-vector-frame-integration-site-descent`
(`Sheaf.Paper.VectorFrameIntegrationSiteDescent`), and
`lem-pur-compact-support-site-coherence`
(`Sheaf.Paper.CompactSupportSiteCoherence`). Their direct proof-dependency edges
are replaced by the existing ordered-integration comparison and the two existing
unique-normalization constructions. These modules may remain needed indirectly
by the unfinished projective/tensor/exponent route or other library consumers;
this delivery does not withdraw them or claim global unreachability.

## Where the brief, the DAG or earlier work was wrong

The four remaining item statements concern arbitrary Noetherian schemes with ell
invertible. The planned P1 and exponent-transport theorems are specialized to
finite-type schemes over the fixed finite field; they cannot simply be applied
to these generic statements. The existing orderedIntegration_comparison theorem
has the required generality and bypasses that mismatch for global integration.

The private normalization helper in ProEtaleVectorIntegration is not a public
API. This delivery proves the needed forward implication locally from functor
naturality and the public ordered-comparison theorem, without adapting that
module. On opens, Noetherianity follows from the induced Noetherian topology;
there is no added finite-type, separatedness, coefficient flatness, nonemptiness,
or positive-rank assumption. Rank zero and the empty base use the same formulas
and the already established unique-normalization theorems.

## Second reading by V6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
