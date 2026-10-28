## What changed

Proved `AlgebraicGeometry.ProEtale.IntegralFiniteScalar.finiteFreeScalarProjection_triangle`
without changing its statement. Flip both tensor bifunctors in the native derived
adjunction's projection-map construction, using the same generic derived tensor
comparison as `tensorPull`. Private helpers identify the resulting map with the
specified `projection` after the pullback comparison and construct a triangle morphism.
Apply it to the point-pulled mapping-cone triangle of `S.f`. Additivity and the given
finite biproduct identifications make the first two components invertible; the target
third object is transported along the prescribed `modelPull` comparison.

Added `Sheaf.Paper.ScalarProjectionTransformation`, whose `scalarFirstProjection`
definition fixes this actual natural transformation once, and two fully proved helper
modules: `Sheaf.Paper.ScalarProjectionTensorUnit` proves
the unit component invertible by oplax left unitality, and
`Sheaf.Paper.ScalarProjectionShift` proves shift compatibility by the existing native
tensor-comparison and adjunction APIs. Both identify the generic tensor comparison
with the native comparison. Keeping these parametric calculations outside the large
scalar-model import context avoids repeated expensive instance comparisons. All new
imports in the item module are private proof imports. No existing public statement,
definition, instance, or public import changes. Only the item's module and proof record,
these three new modules, and their new nodes are delivered.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.IntegralFiniteScalar.finiteFreeScalarProjection_triangle`.
No holes added and no unfinished statements split off. All four delivered modules
contain zero `sorry`.

The two new theorems are also completely proved:
`AlgebraicGeometry.ProEtale.CondensedRing.scalarProjection_tensorUnit_isIso`
(node `lem-sfb-scalar-projection-tensor-unit`) and
`AlgebraicGeometry.ProEtale.CondensedRing.scalarProjection_commShift`
(node `lem-sfb-scalar-projection-shift`). Their private helpers are proved as well.
The finite-biproduct argument includes rank zero through the general biproduct theorem;
no monomorphism condition on `S.f` is needed for its mapping-cone triangle.

## No longer needed

The old planned proof dependencies `lem-weil-pbc-ringed-projection-mate-exact`
(`Sheaf.Paper.ProjectionMateExact`), `lem-sf-ringed-derived-native-tensor`, and
`lem-sf-triangle-morphism-iso` are not used by this proof. Native internal module-object
shift compatibility, tensor exactness, and derived adjunction APIs provide the triangle
construction directly. The triangle two-out-of-three theorem is not needed here because
this statement asks only for the triangle package; its parent applies that theorem.
No original imports were removed. Some old dependencies remain transitively imported
by the unchanged public model-definitions module; this delivery does not claim those
modules have left the targets' import closure. No existing module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The planned transport through ringed modules and a tensor braiding is unnecessary.
Flipping both tensor bifunctors in the existing adjunction projection-map construction
gives the scalar-first order directly. Its shift compatibility follows from the proved
first-variable compatibility of the native tensor comparison. The unit calculation is
oplax left unitality transposed along the native derived adjunction. Using the generic
comparison directly in the transformation preserves the model's specified normalization
and avoids an expensive native/generic conversion inside the final transport equality.
The finite-sum and cone route of the blueprint is retained.

## New nodes

`def-sfb-scalar-first-projection-transformation`, realized by
`Sheaf.Paper.ScalarProjectionTransformation`, is the explicit adjunction construction
of `scalarFirstProjection`. Its body contains no postponed data or proof. Sharing this
definition keeps the functors and tensor structures identical in the three consumers.

`lem-sfb-scalar-projection-tensor-unit`, realized by
`Sheaf.Paper.ScalarProjectionTensorUnit`, records the tensor-unit calculation for the
scalar-first projection for an arbitrary commutative condensed coefficient ring.
Its proof is complete, with no added assumption or postponed step.

`lem-sfb-scalar-projection-shift`, realized by `Sheaf.Paper.ScalarProjectionShift`, records
the shift compatibility of that projection, obtained from the native tensor comparison
and generic adjunction projection-map theorem. Its proof is complete. The item's proof
record now cites the shared construction and these two proved steps. No change record is needed: no other existing
module or node is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteFreeScalarProjectionTriangle": "25d3ffbe901cc4b344a174ce92fa0d0ae813cd81", "Sheaf.Paper.ScalarProjectionShift": "1ea8725366ca6a47f72e2efcc501e4d2f392ff00", "Sheaf.Paper.ScalarProjectionTensorUnit": "a5ee8052b5be298aa1c876ef79d4b515a54e20f9", "Sheaf.Paper.ScalarProjectionTransformation": "d7b1501346e806419fd84f467fa6ba195e0a45be"}, "results": {"Sheaf.Paper.FiniteFreeScalarDerivedComparison": {"hash": "4f41319fd3f7a83e8625167050113e4307a8b6f6", "status": "OK"}}, "seconds": 19, "time": "2026-10-28T13:23:45+0800", "transitive": 0, "version": 1}
```

## Second reading by H6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
