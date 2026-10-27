## What changed

Proved `AlgebraicGeometry.ProEtale.supportComparisonOpenRestrictionAugmentation`
in `Sheaf.Paper.PurityOpenRestrictionAugmentation`. Its original statement and both
canonical open source/resolution constructions are preserved verbatim. The adopted
source localization-restriction instance supplies injective preservation; finite
limits and colimits follow from the restriction adjunctions. Common injectives gives
the restricted augmentation and normalized computation isomorphisms. Unit compatibility
and naturality prove the ordinary augmentation and chain-map equalities. Cancelling
the localized augmentation reduces the final square to derived-unit naturality.
A proved private helper and local irreducibility controls prevent unnecessary
expansion of the canonical comparison construction.

In the unclaimed dependency `Sheaf.Paper.PuritySupportCommonInjectives`, changed only
the body of `supportComparisonSource`: it now uses `HomologicalComplex.single`
directly, instead of the definitionally equal `CochainComplex.singleFunctor` wrapper.
Terms, differentials, degree, bound proof, signatures and mathematical meaning are
identical. This repairs excessive conversion work in the original interfaces.
The unchanged source baseline exceeded 60 seconds; the repaired two-module packet
compiled in 37.3 and 25.3 seconds. Final server validation compiled both delivered modules in 3.1 and 31.6 seconds.
The unchanged consumer compiled in 43.9 seconds against the repaired dependency,
and the item compiled there in 47.3 seconds. The delivery tool runs its own checks. The two dependent modules were identified with `tools/downstream.py`;
`SupportComparisonSectionModel` needs no source edit.

The change is documented in
`coord/changes/purity-open-augmentation-proof-elaboration.md`.
The node records the direct adopted restriction API and the shorter final
cancellation argument. No target or adopted source-library file changes.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.supportComparisonOpenRestrictionAugmentation`
(node `lem-pur-open-restriction-comparison-augmentation`).
Added 0 holes; split off 0 statements. Both delivered Lean modules contain 0 `sorry`.
The common-injectives dependency already had 0 holes, and keeps all its proved bodies.

## No longer needed

Replaced the proof import `Sheaf.AlgebraicGeometry.ProEtaleRestrictionInjectives`
by `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective`.
The latter supplies exactly the localization injective instance used here. The former's
slice equivalence and unbounded derived-evaluation theorem are unnecessary for this
bounded-below restriction argument. Removed
`lem-weil-pbc-proetale-restriction-injectives` from direct proof dependencies and tool uses;
the source API implements its needed injective-preservation part directly.

No direct invocation of `lem-weil-pbc-ring-sheaves-grothendieck`,
`lem-sp-grothendieck-enough-injectives`, or
`lem-weil-pbc-right-derived-plus-injective` is needed: common injectives already
supplies the normalized computation, and augmentation cancellation proves naturality.
Removed these three obsolete direct proof dependencies/tool uses. Also removed the
unused proof imports `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
and `Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives`; the repaired
packet compiled without them in 2.3 and 24.7 seconds. No module is withdrawn or claimed globally unused.
All remaining planned dependencies and the unit route are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect found. Reconstructing both computation isomorphisms
from alpha in the last planned step is unnecessary; their derived-unit equations
and invertibility of the localized augmentation imply the required square directly.
The wrapper for the degree-zero source also caused expensive conversions; using
Mathlib's explicitly documented underlying single functor preserves the construction.
Interrupted compiles and delivery results were checked before continuing. The first delivery of the repaired source timed out on the local compile path and
pushed nothing; the complete packet and unchanged consumer then passed through
the project-server compile path. The first passing delivery was `e594ff26ad7`;
this final packet removes two proof imports confirmed unnecessary by compilation.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
