## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.constructibleExtContinuityStratum`
without changing its signature or public imports. The resumption repaired the injective-embedding monomorphism argument by passing
its two component proofs explicitly to `mono_comp`. Private proved helpers generalize the
existing noetherian closed-costalk, strict costalk-model and finite-free Hom arguments
to qcqs schemes with the given quasi-compact complementary open. The final proof compares
the original canonical cocones and cancels the compatible vertex isomorphism.
The lisse predicate is transported through the canonical coefficient scalar equivalence.
Updated the node proof and proof dependencies to this route. No definitions or existing
consumer modules changed. The resumed preflight requested a command change record;
`coord/changes/E3-constructible-ext-continuity-proof-commands.md` documents the
proof-local commands and lists all transitive consumers. Colimit instances are cached locally; heartbeat options are
scoped to declarations, and development exits and profiler settings are removed. The resumed session
checked the unchanged signature against current sources and updated the theorem
docstring to match the actual six-step costalk proof rather than the superseded plan.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.CondensedRing.constructibleExtContinuityStratum`
(node `det-lem-constructible-ext-continuity-stratum`).
Added 0 holes; split off 0 theorems. No sorry remains in the delivered module.
All private helpers are proved. The resumed `lcompile.py --all` check compiled the
complete module cleanly in 41.5 seconds, then its unchanged direct consumer
`Sheaf.Paper.ConstructibleExtContinuity` in 4.5 seconds, with zero errors and warnings.
The first resumed delivery dry run also passed compilation and its axiom probe; its
only preflight diagnostic requested the command change record now supplied. Imported
statements retain their existing proof obligations.

## No longer needed

Removed direct imports from the current library version (some remain available
transitively through required APIs):

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.AlgebraicGeometry.CondensedClosedSupportAdjunction`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`
- `WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution`
- `Sheaf.AlgebraicGeometry.ProEtaleBoundedContinuitySections`
- `WeilConjectures.CategoryTheory.TruncationHypercohomology`
- `WeilConjectures.CategoryTheory.TruncationTriangle`
- `Sheaf.AlgebraicGeometry.BoundedContinuityDirectImage`
- `Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit`

The development-only direct import `Sheaf.Paper.CondensedFiniteFreeHomEvaluation`
was also removed in the earlier attempt.

The following old direct proof dependencies are replaced by the compatible strict-costalk
model and the existing condensed-coefficient continuity APIs. Their general spectral
sequence construction and the ring-sheaf conversion are not re-proved here:

- `def-weil-closed-immersion`
- `def-weil-open-immersion`
- `sk-prop-sfb-cartesian-coefficients`
- `sk-def-sfb-module-pushforward-pullback`
- `def-pur-sheaf-tensor-product`
- `def-weil-sheaf-of-modules-category`
- `lem-sf-exact-functor-derived-triangulated`
- `det-sf-open-closed-sequence-ring-sheaf`
- `det-lem-formal-closed-support-stratum-hom`
- `lem-pc-right-derived-functor-triangulated`
- `lem-pur-ringed-site-grothendieck-abelian`
- `det-pe-bounded-continuity-sections`
- `thm-sp-truncation-e2`
- `lem-weil-pbc-truncation-triangle`
- `det-lem-bounded-continuity-direct-image`
- `lem-weil-pbc-filtered-colimits-commute-finite-limits`

Removed obsolete tool_uses approvals: `lem-pur-ringed-site-grothendieck-abelian`, `lem-pc-right-derived-functor-triangulated`, `lem-sf-exact-functor-derived-triangulated`, `thm-sp-truncation-e2`, `lem-weil-pbc-truncation-triangle`, `lem-weil-pbc-filtered-colimits-commute-finite-limits`, `det-pe-bounded-continuity-sections`.
No module is withdrawn, and no global reachability claim is made: shared users may still
need these nodes. The unit has no realized statement or proof-step nodes to bypass.

## Where the brief, the DAG or earlier work was wrong

The earlier sandbox contained a development `#exit`, no report, and an incomplete
injective-embedding monomorphism argument. The named existing costalk-model and finite-free
Hom continuity theorems assume noetherianity, which is absent here. Their proofs use it
only to obtain qcqs geometry and a quasi-compact open complement; these are supplied by
this item's actual hypotheses. The private generalizations keep every hypothesis of the
item unchanged. The admissibility binder is retained, although this argument works for
all commutative condensed coefficient rings. Empty schemes and rank-zero modules use the
same constructions, and no arbitrary witness of an unproved existence theorem defines data.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
