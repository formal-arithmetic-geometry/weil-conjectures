## What changed

Restored `lean/Sheaf/AlgebraicGeometry/TensorCoordinateIdentifications.lean` as a compatibility module importing the adopted source implementation. The adopted source already contains the complete proof of `AlgebraicGeometry.exists_tensor_coordinate_identifications`; the compatibility path preserves the legacy `IsAcyclicTensorKFlat` API through the existing canonical comparison import. Updated the sandbox DAG copy to attach the existing source declaration and added `coord/changes/tensor-coordinate-identifications-source-compatibility.md`.

## Proved and sorry left

The item had zero `sorry`s in its quarantined archive and adds zero `sorry`s. The adopted declaration `AlgebraicGeometry.exists_tensor_coordinate_identifications` is complete and has no additional holes.

## No longer needed

The archived private helpers `counit_isIso`, `modelMap_isIso`, `modelMap_natural`, and `tensor_representation_algebra` are no longer duplicated: the adopted source has its own complete proof infrastructure. The withdrawn Sheaf K-flat proof imports are unnecessary for this compatibility module. No DAG proof step is pruned; the theorem remains attached to the same unit route.

## Where the brief, the DAG or earlier work was wrong

The quarantined archive was stale after the source twin migration: its proof referred to `CochainComplex.isKFlat_pullback` from the withdrawn Sheaf K-flat module, causing the recorded global-build failure. The current adopted source uses `IsKFlatTensor` and the source K-flat API. This is an API migration issue, not a mathematical change. A direct signature audit and the archived tensor-stalk consumer audit compile against the repaired path.


Validation: the restored module and the archived direct consumer compile in import order (5.4 s and 0.1 s). The consumer differs only in its separately retired SingleComplexBaseChangeStalkCondition import and is excluded from the delivery. The complete archived signature audit also compiles against the adopted source theorem (9.8 s).

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
