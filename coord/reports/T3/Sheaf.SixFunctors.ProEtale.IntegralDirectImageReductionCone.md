## What changed

Proved `AlgebraicGeometry.ProEtale.integral_direct_image_reduction_cone` without
changing its signature or `integralFiniteProjection`. The finite coefficient is
dualizable by the existing two-term uniformizer resolution. The generic
projection theorem and the existing scalar-mate interface therefore make the
specified finite projection invertible. Explicit private mate-transport lemmas
identify the interface mate with the exact geometric mate used in this item.
Tensoring the resolution constructs the first distinguished triangle; transport
along the restricted projection constructs the second and proves both squares.

Only this module and its existing DAG proof record change. All additional imports
are private proof imports. Private instance caches keep the derived tensor
elaboration compact. The normalized comparison calculation is checked over general coefficient rings
and then specialized, avoiding repeated concrete reductions. No heartbeat or file
time limit is increased.
No public definitions, statements, public imports, consumers,
or unit realizations change.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.integral_direct_image_reduction_cone`
(node `lem-sfb-integral-direct-image-reduction-cone`).

There are zero holes left in the delivered module and zero added holes. No
statements are split off. The proof uses existing declarations, including the
existing unfinished `QuotientChange.internal_scalar_mate_projection`; it adds no
assumption or replacement for that dependency.

## No longer needed

Removed the direct proof import `Sheaf.Paper.ModuleRingedToposDerivedComparison`
and its direct proof dependency `lem-pd-module-ringed-topos-derived-comparison`:
the scalar interface supplies the needed mate comparison. That module remains a
transitive dependency and is not withdrawn.

Removed the redundant direct import `Sheaf.Paper.InternalScalarMateProjection`: it
is already publicly imported by `NormalizedScalarRestrictionPush`, and its
`internal_scalar_mate_projection` theorem remains used.

The theorem `integral_reduction_pullback_normalization` is not used in this proof;
the input already assumes invertibility of its specified map. Its module and the
node `lem-sfb-integral-reduction-pullback-normalization` remain required for the
map's definition and the unchanged statement, so they are not withdrawn.

The former proposed direct-image-of-cone identification and sectionwise comparison
are replaced by dualizability and explicit transport. No library module or DAG
node is withdrawn; no source-library declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The old proof sketch describes applying direct image to a scalar triangle and
identifying its finite vertex. The existing APIs also permit a shorter independent
route: the two-term resolution gives dualizability, and the general adjunction
projection theorem gives the finite comparison before triangle transport. This
uses no result from the parent `IntegralDirectImageLimits` and creates no import
cycle. The DAG proof and proof dependencies now record this route. The unit's
realized route is unchanged.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
