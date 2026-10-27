## What changed

Proved `vectorFrameIntegrationSiteDescent` using the existing ordinary trace normalization,
ordinary geometric concentration and invertibility, the uniquely normalized pro-etale
integration, and degree-zero map gluing. The proof transports the prescribed maps through
the actual compactification and site isomorphisms. It gives the all-frame restriction
formula before using gluing, so independence of the cover and the empty-cover case follow
from the same argument.

Proved `frameActionSiteDescent` by compact-support exchange transport on the bounded Tate
input, naturality in the canonical coefficient map, the ordinary bounded/unbounded exchange
compatibility, and derived identity coherence. Fully proved private helpers keep the
comparison maps folded. The final step composes with the prescribed compactification change;
it does not redefine either action through conjugation.

Proved `finiteTypeVectorFrameIntegrationSiteDescent` by obtaining the Noetherian instance
from finite type over the coefficient field and the unit condition from stalkwise
invertibility, then applying the descent and action statements on every open.

Updated the existing node's proof and direct proof dependencies to describe the shorter
route. All existing signatures and public imports are unchanged. The bounded input keeps its original underlying object and uses a proved generic
boundedness witness. It is now irreducible with the proved defining equality
`frameActionInput_obj`. The canonical coefficient map is expressed through that equality
by `frameActionCoefficient`. The generic definitions `frameActionEtaleComposite` and
`frameActionProComposite` retain the original independent compositions and arrow order.
These APIs avoid repeatedly unfolding the concrete Tate tower during kernel checking;
see `coord/changes/Q1-frame-action-input-single.md` and
`coord/changes/Q1-frame-action-sharing.md`. The downstream module held by V7 uses none
of the changed definitions and needs no adaptation.
Added private proof imports for ordinary geometric descent, degree-zero normalization,
derived-functor coherence, the bounded pullback comparison, and its underived identity.
Proof documentation is updated to match the implemented route. No source-library files
or consumer interfaces are changed.

## Proved and sorry left

Closed all three original holes, belonging to
`lem-pur-vector-frame-integration-site-descent`:

- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorFrameIntegrationSiteDescent`;
- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.frameActionSiteDescent`;
- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.finiteTypeVectorFrameIntegrationSiteDescent`.

There are zero remaining holes in the item, zero holes added, and zero split-off statements.
All private helpers are fully proved. The final complete module compiles cleanly through
`lcompile.py` (52.7 seconds, exit code 0, no warnings). Profiling identified repeated
boundedness and comparison endpoint unfolding. The generic action formulas and the
explicit defining-equality API remove this repeated work. All five new public API
helpers are attached to the existing node; no new mathematical dependency is introduced.
A separate equality test of both final action definitions against their original literal
formulas compiles cleanly in 12.4 seconds, using only unfolding, equality transport
simplification, functor identity and category identity laws.
Existing unproved imported theorems are used as the declared dependencies permitted by
stage 3; this does not claim their proofs are completed here.

## No longer needed

The direct frame-descent proof no longer repeats the symmetric-algebra/relative-Proj
construction, ordinary linear trace invariance, finite-torsion base change, or the
common-refinement construction. It reuses the already stated normalization, concentration,
and compactification-comparison APIs. These results and their source declarations remain
in the library and may still be needed transitively or by other consumers.

The obsolete direct proof dependencies are `def-asd-vector-bundle-zero-section`
(already part of the unchanged statement dependencies),
`def-sfb-relative-proj-iso-of-graded-iso`,
`lem-amb-affine-space-top-trace`, `lem-amb-finite-tate-site-descent`,
`lem-amb-linear-trace-invariance`, `lem-amb-vector-projective-completion`,
`lem-cbc-compactifiable-cofiltered`, `lem-pur-compact-support-site-coherence`,
`lem-sf-comparison-pullback-exact`,
`lem-weil-pbc-quasi-coherent-symmetric-algebra-core`, and `thm-cbc-finite-torsion`.
Removed private proof imports:
`WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`,
`Sheaf.AlgebraicGeometry.AffineSpaceLinearTraceInvariance`,
`WeilConjectures.Compactification.CategoryBaseChange`,
`Sheaf.AlgebraicGeometry.QuasiCoherentSymmetricAlgebraCore`, and
`Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`, and
`Sheaf.Paper.ComparisonPullbackExact`. Exactness of the fixed-module comparison is
already supplied by the adopted comparison functor instances.

Their obsolete top-level tool approvals are removed in their original order; approvals
for the dependencies retained by the proof remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The private exact-functor identity calculation follows the already proved private
`exact_identity_square` argument in `Sheaf.Paper.OpenScalarSiteCoherence`; it is
instantiated here for inverse-image functors rather than open extension.

No statement is disputed. The DAG planned to redo geometric and gluing arguments already
available through the ordinary normalized trace and the uniquely normalized pro-etale
integration. Those existing declarations give a shorter proof without changing the unit
route, any hypothesis, or any conclusion. Both relevant unit records have empty realized
statement and step lists. Rank zero, empty schemes, empty covers, nonaffine opens, and
nonseparated Noetherian bases need no added assumptions.

## Second reading by Q1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
