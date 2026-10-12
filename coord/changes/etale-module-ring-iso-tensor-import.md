# EtaleModuleRingIsoTensor public imports

## Reason
The proof does not use the inverse-image algebraic-structures construction. Its
site and sheafification instances are supplied by Mathlib's affine etale site;
retaining the project inverse-image module unnecessarily exposed a large
unrelated interface to the sole downstream importer.

## Old
```lean
public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
```
These are the original import lines of the item.

## New
```lean
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
```
The item's existing TensorProduct and PushforwardContinuous public imports are
unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleModuleInverseImageTransport | not recorded locally | It imports EtaleModuleRingIsoTensor for `etaleModuleRingIsoTensor`; it already imports EtaleInverseImageAlgebraicStructures directly and publicly. Hence that interface remains available to it and its downstream users without any adaptation. Its existing statement is unchanged; no target definition changes. |

## Status
landed 20261012T112834-L-765900 2026-10-12 (merge of deliver/E1/Sheaf.AlgebraicGeometry.EtaleModuleRingIsoTensor)
