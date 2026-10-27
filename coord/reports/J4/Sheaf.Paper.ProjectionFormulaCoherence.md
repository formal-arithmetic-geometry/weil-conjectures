## What changed

Used the current source of the assigned rework module, preserving its public declarations
and remaining mathematical obligations. The initial source and quarantined copy were identical.
The original source compiles against the current publication (49.9 seconds), so the
historical upstream-import failure no longer reproduces.

Reduced `WeilConjectures.sixFunctorProjection_baseChange_finite` to the existing canonical
fixed-scalar diamond and a separate theorem identifying each realized route. The proof
reflects equality through the full inclusion and cancels the explicitly constructed
target isomorphism, using the proved generic private helper `reflectProjectionPaths`
in `ProjectionFiniteBaseChangeTransport`. The item applies that completely proved
transport theorem. It adds no separatedness assumption on the horizontal map. The
canonical diamond proof retains the proper/open factor argument required by the unit.

Relocated the existing finite tensor-realization, monoidality and exchange definitions
verbatim to `Sheaf.Paper.ProjectionFiniteBaseChangeCoordinates`, publicly reexported by
the item. Added definitions of the two routes and their shared endpoint comparisons.
No source-library declaration or target changes; all original public signatures stay
identical. The private tensor-action helper is extracted as described below. No consumer needs
adaptation: there are no current or quarantined direct importers of this item.

Change records: `coord/changes/J4-finite-projection-base-change-coordinates.md` and
`coord/changes/J4-projection-tensor-action-expansion.md`.

All five delivered Lean files were validated with `lcompile.py`; the final item
passes cleanly in 39.9 seconds. All original public declaration signatures match
the initial source. The delivery tools perform their independent checks as well.

## Proved and sorry left

One of the original eight holes is reduced:
`WeilConjectures.sixFunctorProjection_baseChange_finite` (node `prop-sf-pf-coherence`).
Its combining proof is complete. This is a decomposition, not a net hole closure:
one original hole is closed and one strictly smaller coordinate-compatibility hole
is added. No other existing proof is replaced by a postponed proof.

The seven original holes left in the item, all on `prop-sf-pf-coherence`, are:

- `WeilConjectures.sixFunctorProjection_baseChange_integral`
- `WeilConjectures.sixFunctorProjection_baseChange_rational`
- `WeilConjectures.sixFunctorProjection_baseChange_common`
- `WeilConjectures.sixFunctorProjection_identity`
- `WeilConjectures.sixFunctorProjection_reduction_integral`
- `WeilConjectures.sixFunctorProjection_reduction_rational`
- `WeilConjectures.sixFunctorProjection_reduction_common`

The one added hole is
`WeilConjectures.sixFunctorProjectionFinite_routes_realization`, node
`lem-sf-finite-base-change-route-realization`, in its own new module. It states
separate equations for the images of the two paths under the prescribed realization.
It does not assert their equality; the existing canonical diamond is independently
needed to complete the item proof. Its docstring gives the normalization and
unit/counit cancellation argument and its edge cases.

The coordinate, transport and tensor-action expansion modules have zero holes. Total holes in delivered files: eight.
The transport theorem is fully proved from the route equations and the existing diamond;
it is not an additional postponed version of the item. Its separate module keeps the
item within the file compile limit.

The existing private `genericProjection_tensorAction` is replaced by the fully proved
public equation `projectionTensorCoordinateComponent_tensorAction` in
`Sheaf.Paper.ProjectionTensorActionExpansion`. It applies the generic
`splitProjectionActionImage` lemma to expand the image of a composite, preserving
the same tensor-action equation and dependencies. This self-contained calculation is
separated to distribute work out of the item. Focused profiling identifies the remaining
large kernel cost as `fixedComponent_eq`, not this neighboring tensor-action helper.
That private proof now uses reflexivity directly: all differing instance arguments are
propositions, so the explicit equality transports from its three case splits are
unnecessary. The final cleaned item compiled in 39.9 seconds, with no errors or warnings.
Its proof uses the already proved arbitrary-coefficient-category private library lemma
`AlgebraicGeometry.ProEtale.genericProjectionAction_compactification`, whose Lean
signature already quantifies over arbitrary coefficient categories.

## No longer needed

Removed the proof-only `import all Sheaf.Paper.FiniteProjectionActionLaws` from the
item: the tensor-action expansion now accesses that private proof in its own module.
Also removed `import all Sheaf.Paper.ConstructibleProjectionMates`: the private
generated proof names were used only by the now-unnecessary instance case splits.
The original public import of the same module remains necessary for the statements.
No original mathematical dependency node or module is pruned in this partial delivery;
the remaining coefficient clauses still need their recorded dependencies. In particular,
the open-factor and compactification-pasting nodes remain on the unit route.

## Where the brief, the DAG or earlier work was wrong

The rework entry records an upstream projection-formula import failure, but the
unmodified archived/current source now compiles. The delivery therefore makes an
actual finite base-change reduction, rather than treating a rebase or a no-op as the
repair. The existing fixed-scalar diamond already gives the canonical geometric
calculation; its realization into this item's operation coordinates is the remaining
finite step. The canonical diamond is used as a tool from
`lem-sf-finite-projection-exchange-transposes` (unit `sk-thm-sf-compatibility`):
its fixed-scalar proper transposes and open assembly give the very same factor
calculation, rather than a new route around the current unit's realized steps.

## New nodes

`def-sf-finite-base-change-realization-paths` records the unchanged finite coordinate
definitions and the constructed paths and common endpoint comparisons. The comparisons
are compositions of the specified isomorphisms, including equivalence units; none
is an arbitrary witness of existence.

`lem-sf-projection-tensor-coordinate-action` records the fully proved expansion of
the existing generic compactification tensor-action equation. It uses the same
canonical coefficient structures, source and target, with the final functor image
written as the composite of two images. It introduces no new proof obligation.

`lem-sf-finite-base-change-transport` is the fully proved faithful-reflection calculation
in its own module. Its source and conclusion are the finite square of the same unit;
its proof combines the coordinate lemma with the existing canonical diamond.

`lem-sf-finite-base-change-route-realization` states the two independent coordinate
identifications. Its source is the base-change paragraph of the current blueprint,
expanded using the existing constructible projection and finite-compositor
normalizations. Searches found the generic faithful-functor API and the existing
fixed-scalar diamond, but no theorem identifying these specific coordinate paths.

Change records: `coord/changes/J4-finite-projection-base-change-coordinates.md` and
`coord/changes/J4-projection-tensor-action-expansion.md`.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
