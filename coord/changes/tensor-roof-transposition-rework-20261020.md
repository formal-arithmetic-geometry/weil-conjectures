# AlgebraicGeometry.Scheme.tensor_roof_transposition

## Reason

Restore the assigned quarantined module from
`quarantine/Sheaf/AlgebraicGeometry/TensorRoofTransposition.lean`.
The rework record reports `Unknown identifier Scheme`: the archived public import
of `Sheaf.AlgebraicGeometry.DerivedTensorAugmentation` now names an empty withdrawn
module. The statement needs the original K-flat predicate and scheme derived
tensor structure directly. Its proof does not use a tensor augmentation definition.

## Old

The archived import block, verbatim:

```lean
public import Sheaf.AlgebraicGeometry.DerivedTensorAugmentation
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction
```

## New

```lean
public import Sheaf.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction
```

Everything following the import block is byte-for-byte identical to the archive:
all theorem signatures, proof bodies, docstrings, attributes and options remain.
No definition changes; no target meaning changes. The existing Lean attachment,
proof dependencies and unit route are retained. There are zero holes.

## Users

`tools/downstream.py` reports the item as an unknown module, since it is quarantined.
A search of `lean/` and `quarantine/` finds exactly one importing source file.
The source-library theorem of the same name and its source-library consumer use
the separate upstream module, which is neither imported nor changed here.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.TensorRoofTransposition | B3 | Restore with direct statement imports; declarations and proofs unchanged. |
| Sheaf.AlgebraicGeometry.AffinePerfectTensorRoof | unclaimed; quarantined | Same theorem and argument types; no adaptation forced by this import repair. |

The archived consumer was compiled as a scratch check. It fails before its proof,
with an existing collision between `Sheaf.AlgebraicGeometry.PerfectComplex` and
`WeilConjectures.AlgebraicGeometry.PerfectComplex`, both defining
`AlgebraicGeometry.Scheme.IsPerfect`. That independent quarantine defect is not
changed by this packet. A dedicated public-import consumer checks the repaired
module's exposed statement dependencies and theorem.

## Status

landed 20261020T160104-L-3325122 2026-10-20 (merge of deliver/B3/Sheaf.AlgebraicGeometry.TensorRoofTransposition)
