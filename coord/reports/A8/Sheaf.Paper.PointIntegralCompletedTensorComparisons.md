## What changed

Replaced the single hole in `WeilConjectures.pointIntegralCompletedTensorComparisons`
with fieldwise assembly from a normalized chain augmentation, derived monoidal
descent, and scalar compatibility. Added three modules and corresponding nodes.
The original theorem signature and all existing definitions are unchanged.
The item privately imports `Sheaf.Paper.PointIntegralTensorChain`,
`Sheaf.Paper.PointIntegralTensorDescent` and
`Sheaf.Paper.PointIntegralTensorScalarCompatibility`. The chain module publicly
imports the existing model interface and privately imports all of
`Sheaf.Paper.PointSheafHomMaps`, `Sheaf.Paper.IntegralAmbientOperationModels`
and `Mathlib.CategoryTheory.Limits.HasLimits`, to use the proved sections tensor
map, normalized augmentation and chosen-limit conversions.

The chain augmentation is the ordinary tensor map on sections followed by
`IntegralAmbient.tensorOperationUnit`. Its quotient coordinate follows from
`augmentation_existsUnique`, `tensorTowerModel` and the sections tensor formula;
its shifted coordinate follows from `tensorOperationUnit_coordinates`.

## Proved and sorry left

Closed the original hole in `WeilConjectures.pointIntegralCompletedTensorComparisons`
by decomposition. Proved `WeilConjectures.pointIntegralTensorChain` from the existing
sections tensor and normalized sheaf augmentation APIs.

Added two holes, each in a new public theorem with its source and proof in words:

- `WeilConjectures.pointIntegralTensorDescent`, node
  `lem-sf-point-integral-tensor-descent`: descent of an already normalized chain map
  to the derived monoidal comparison and constant-section unit, for one field.
- `WeilConjectures.pointIntegralTensorScalarCompatibility`, node
  `lem-sf-point-integral-tensor-scalar-compatibility`: the scalar square for any
  already canonical integral tensor witnesses.

There are no holes in definitions or private helpers. This closes one upper hole
and adds two strictly smaller obligations; it is a decomposition, not a net proof.
Imported declarations may retain their pre-existing holes.

## No longer needed

No original public imports were removed. No module is withdrawn and no global
pruning is claimed. The original finiteness, perfectness, exact-products, reduction,
and scalar-comparison dependencies remain needed by the two intermediate proofs;
the parent node now records the three direct steps instead. The chain construction
uses the already normalized sheaf tensor augmentation instead of reconstructing
its finite quotient coordinates from derived perfect models.

`lem-weil-point-sections-scalar-extension` is unnecessary for the scalar square:
that predicate is an identity of chain representatives, proved from the normalized
finite scalar tensor maps and the two Roos coordinates. The derived scalar fibre
comparison is not part of this particular predicate. Its module has other users
and is not withdrawn.

## Where the brief, the DAG or earlier work was wrong

The node's plan mixes the construction of the chain augmentation with proving its
derived invertibility. The existing `IntegralAmbient.tensorOperationUnit` already
constructs the sheaf augmentation and proves both coordinates. Applying the
sections tensor map supplies the required point chain map without a perfect-model
choice. Perfectness is needed later for derived invertibility, not for this map.
The scalar-square predicate uses only the completion fields of its witnesses.
No mathematical statement dispute or interface repair is asserted.

## New nodes

`lem-sf-point-integral-tensor-chain`: existence of the actual normalized chain
augmentation; proved, with no monoidal or scalar assertion.

`lem-sf-point-integral-tensor-descent`: the single-field derived monoidal and unit
construction from an already normalized completion map. This does not construct
that chain map or assert any coefficient-change square.

`lem-sf-point-integral-tensor-scalar-compatibility`: scalar compatibility of any
already canonical witnesses, proved by first and shifted Roos coordinates. This
constructs neither the maps nor the monoidal data.

The unit route is unchanged; its realized statement and step lists are empty.
No definition change records or forced consumer adaptations are needed.

## Second reading by A8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
