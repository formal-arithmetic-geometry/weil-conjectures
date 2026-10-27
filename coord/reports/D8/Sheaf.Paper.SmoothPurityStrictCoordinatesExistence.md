## What changed

Replaced `strictCoordinatesExistence`'s single `sorry` with an assembly of the
actual base, geometric coordinates, and normalized open tensor construction.
Its statement and public imports are unchanged. All three new imports are private
proof imports.

`SmoothPurityStrictBaseCoordinates.strictBaseCoordinates` is proved: it factors
ell in the specified integer DVR, proves the exponent positive, identifies the
quotient ideals and proves finiteness. It constructs the equivalence to the
existing sequence-site systems by equality transport of the ring presheaf and
rebundling only the sheaf-condition proof. Separate proved helpers verify that
sections, all restrictions, and all morphisms are unchanged, and that the functor
is additive. It retains the systems field of semilinear derived sections and uses
its Grothendieck structure for K-injective resolutions.

The item constructs derived composition by exact termwise localization of the
ordinary compositor. For open tensor it forms the specified unit/tensor-pullback
arrow, takes its actual adjunction transpose, and inverts that arrow using the
open-support invertibility result. `openTensor_mate` is the hom-equivalence's
`apply_symm_apply` identity; an arbitrary tensor isomorphism is never substituted.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProEtale.SpTowerShriek.strictCoordinatesExistence`
(`lem-sp-strict-coordinates-existence`). The item now has zero `sorry` tokens.

Also proved
`AlgebraicGeometry.ProEtale.SpTowerShriek.strictBaseCoordinates`
(`lem-sp-strict-base-coordinates`), with zero new holes in that module.

Added two strictly narrower holes, each a public theorem in its own module:

- `AlgebraicGeometry.ProEtale.SpTowerShriek.strictGeometricCoordinates`
  (`lem-sp-strict-geometric-coordinates`): fixed-calculus geometric transport and
  ordinary inverse-image composition with its localized finite evaluation. It
  constructs neither Base nor any open extension or tensor comparison.
- `AlgebraicGeometry.ProEtale.SpTowerShriek.strictOpenTensorCoordinates`
  (`lem-sp-strict-open-tensor-coordinates`): exact open extension and invertibility
  of the specified tensor transpose, for one given open immersion and its given
  Geometry. It constructs neither Base nor geometry on other maps or composition.

This is a decomposition, not a complete proof without additional assumptions:
one old hole closed, two lower holes added, net minus one hole. Both lower
statements retain the actual ordinary categories, normalized adjunctions and
maps; they do not repackage the original existential assertion. Their docstrings
and nodes give the complete construction in words. No axiom or definition hole
is added.

Validation: all four modules compiled together through `lcompile.py`. The original
item and base module have no `sorry`; each remaining construction module has
exactly its named public theorem hole. The final base version also removes all
development profiling options and compiled successfully in 27.7 seconds.

## No longer needed

No existing import was removed and no module is withdrawn. No unit route is
bypassed. The original node now depends immediately on the proved base step and
the two narrower construction steps; its original mathematical dependencies
remain below these steps.

The theorem `sp_coefficient_towers_abelian` is not needed to produce the
section-preserving base equivalence: direct rebundling proves that equivalence.
Its module remains needed for the coefficient definitions in the existing public
interface, so this does not prune that module or its dependencies.

## Where the brief, the DAG or earlier work was wrong

The cited `semilinearDerivedSections` constructs geometry on an inverse-image
coefficient tower and a selected target calculus. Its type does not directly
provide equality to the literal constant quotient tower and the separately fixed
target calculus, or the dependent equality of both finite functors and their
adjunction required by `Geometry.levelAdjunction_eq`. Likewise the open
normalization theorem gives a normalized ringed-site model; transporting that
model into this specified Geometry is a genuine construction step. The two new
statements isolate these parts rather than applying an unrelated existence theorem.

The repeated earlier splits had left the complete arithmetic and base rebundling
inside one hole together with geometry and open support. The base part is now
proved, and the assembly from the two remaining parts is explicit Lean.

## New nodes

`lem-sp-strict-base-coordinates` records the proved arithmetic, section-preserving
rebundling, and retained semilinear calculus. Its source is paragraph (2) of the
current blueprint operations proof, with Zheng Construction 4.1.

`lem-sp-strict-geometric-coordinates` records constant-section transport with
ordinary inverse-image composition and its exact localization. It is a strict
part of paragraph (2), omitting Base and all open operations.

`lem-sp-strict-open-tensor-coordinates` records exact open extension and
invertibility of its specified tensor transpose on the actual sequence site,
using the system case of openTensorNormalization. It is the open-support part
of paragraph (2). Empty/identity opens and zero objects are included; no flatness
of coefficient transitions is assumed.

All nodes preserve the existing chapter and unit. Searches used LeanFinder,
LeanSearch, Loogle and Mathlib/project source grep. No shared definition or
existing interface changed, so no change record or consumer adaptation is needed.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
