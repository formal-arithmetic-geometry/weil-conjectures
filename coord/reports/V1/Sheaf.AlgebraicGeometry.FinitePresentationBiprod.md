## What changed

Proved AlgebraicGeometry.RingedSpace.isFinitePresentation_biprod without changing its
signature or public imports. A proved private helper applies the existing source-library
Presentation.sigma/isFinite_sigma to the two supplied finite presentations, indexed by
ULift WalkingPair. Sigma.reindex and biprod.isoCoprod identify this coproduct with the
binary biproduct. The main proof intersects the presentation covers, maps both presentations
by restriction, identifies the restricted biproduct, and applies finite-presentation locality.
Private imports provide the source library's presentation API and Mathlib's biproduct API.
The node now records this shorter implementation. No source-library module is changed.
Validation: lcompile.py compiled the final item in 22.4 seconds, with no warnings or errors.
The existing theorem statement and public imports were checked unchanged.

## Proved and sorry left

Closed the one original hole: AlgebraicGeometry.RingedSpace.isFinitePresentation_biprod
(lem-weil-pbc-module-finite-presentation-direct-sum). Zero holes remain in the item;
zero holes added and zero statements split off. The private finite_biprod_presentation
helper is proved. The final route uses the already proved source-library coproduct
presentation construction rather than the holed binary cokernel dependency.

## No longer needed

Removed private imports Sheaf.Topology.ModuleColimitRestriction and
Sheaf.CategoryTheory.RingedSiteModules. The proof does not need the former module's
sheafification-of-sectionwise-colimit comparison: Mathlib's restriction adjunctions and
existing preservation instances supply the preservation needed here directly.
Removed lem-weil-pbc-ringed-space-colimit-restriction from this node's proof dependencies.
The latter module supplies an alias unused by this proof; the general module-sheaf
category itself remains needed.

The planned lem-weil-pbc-biproduct-cokernel-cofork and its module
Sheaf.CategoryTheory.BiprodCokernelCofork are also unnecessary for this proof: the existing
proved Presentation.sigma/isFinite_sigma already assembles finite coproduct presentations.
Its import was tested during development but is absent from the delivered file, and the
node's dependency is removed. No declaration or module is withdrawn; other consumers
may still need all of these modules. All other planned dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

No statement error. The source library already supplies Presentation.sigma/isFinite_sigma,
Presentation.isFinite_map, Presentation.isFinitePresentation and
IsFinitePresentation.of_coversTop, avoiding a new block-cokernel proof and reimplementation
of finiteness and locality. The unit's statement and route are unchanged. Empty spaces
are handled by the cover argument, and zero ranks are included in the finite-index APIs.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
