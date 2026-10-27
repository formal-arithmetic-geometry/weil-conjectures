# Profinite.CondensedAction tensor induction data

## Reason

The original item defines both the concrete balanced quotient and the theorem
whose construction needs separate modules. Those modules must refer to the
quotient and the existing specification without importing the theorem back.
Move the original declaration block verbatim into the new
Sheaf.CategoryTheory.CondensedTensorInductionData module and publicly reexport it
from the item. This is a dependency-cycle extraction, not a compile-time split.
Add TensorInductionSheafData as an intermediate specification without additivity,
an adjunction, a Hom equivalence or any extension property. It records the ordinary
sheafified functor, equivariant unit, generator map formula, and the linear
H-equivariant identity tensor. No existing definition or statement changes meaning.

## Old

The item's public header was:

```lean
public import Sheaf.CategoryTheory.CondensedActionModule
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
```

The declaration block from inductionSectionRing through
TensorInductionSheafAdjunction occurred directly in the item. Its signatures,
attributes, data bodies and docstrings are retained verbatim in the new data
module; it is not replaced by newly chosen data.

## New

```lean
public import Sheaf.CategoryTheory.CondensedTensorInductionData
```

The new data module publicly imports every old public import. Consequently every
old declaration and imported interface remains visible from the item. The item
privately imports the concrete presheaf construction, tensor sheafification and
existence-only extension modules. Its old theorem statement is verbatim.

## Users

Read-only tools/downstream.py reports zero current Lean downstream modules, and
an exact import-line search agrees. Pending DAG parents still need this theorem;
the item is preserved, not withdrawn. All original names remain available through
the same original module. No existing module other than the item is modified.
There are no direct importers to compile or adapt.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.CondensedTensorInductionAdjunction | E2 | All old data reexported verbatim; reciprocity assembled from smaller construction steps |

## Status

landed 20261026T081602-L-2013109 2026-10-26 (merge of deliver/E2/Sheaf.CategoryTheory.CondensedTensorInductionAdjunction)
