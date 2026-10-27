## What changed

Filled the three remaining theorem proofs in
`Sheaf.Paper.PbcCompletedPullbackActual`, preserving every existing public
signature, definition, attribute and public import.

* `pbcActualCompleteInclusion_isRightAdjoint` transports the existing Koszul
  reflector to the actual intrinsic-completeness predicate and constructs its
  adjunction from the reflection Hom equivalences.
* `pbcActualCompletionShift_exists` proves shift stability through the existing
  Cech comparison and internal-Hom shift structure. The adjunction supplies the
  shift structure; its unit and reflection injectivity prove uniqueness.
* `pbcActualDirectCompletionIso_exists` identifies the actual reflector with
  quotient-tower completion by its unit. It transports the existing tower
  projection and derived-limit comparison and proves uniqueness by reflection.

Added only private proved transport/reflection helpers and private proof imports.
No source-library module or consumer is changed. No definition or statement repair
is required. The construction works also for the empty scheme and the zero ideal;
no nonemptiness or regular-sequence assumption was introduced.

## Proved and sorry left

Closed all 3 original holes:

* `AlgebraicGeometry.Scheme.pbcActualCompleteInclusion_isRightAdjoint`.
* `AlgebraicGeometry.Scheme.pbcActualCompletionShift_exists`.
* `AlgebraicGeometry.Scheme.pbcActualDirectCompletionIso_exists`.

Holes added: 0. Holes remaining in the item: 0. Split-off statements: 0.
The proofs use existing library declarations, including the completion reflector
and its comparison theorems; this reports the item's holes, not an assertion that
all transitive dependencies are already free of `sorry`.

## No longer needed

No existing import, node or module is withdrawn. Two candidate proof imports,
`Sheaf.Paper.ExtendedCechCompletionModel` and
`Sheaf.Paper.CompletedQuotientUnitNormalization`, were removed as unused: the
former API is unnecessary and the quotient unit is constructed directly from
the published constant-tower adjunction and reduction augmentation. The proof reuses the existing
Koszul reflector, Cech comparison, Koszul/quotient comparison and direct-image
limit API instead of rebuilding their arguments in this module. No unused new
statement module is introduced.

## Where the brief, the DAG or earlier work was wrong

There is no current DAG node whose `lean.module` is
`Sheaf.Paper.PbcCompletedPullbackActual`. Its existing docstrings cite
`lem-weil-pbc-ringed-topoi-module-adjunction`, whose attached declaration and
statement concern the general underived module adjunction rather than these
completion theorems. That unrelated node is preserved. This proof-only delivery
adds no public statement and does not change the unit route.

## Second reading by M7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
