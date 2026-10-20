# Sheaf.AlgebraicGeometry.PseudoCoherentFiberFiniteFreeModel imports

## Reason

The dependency module `Sheaf.AlgebraicGeometry.PseudoCoherentFiberBoundedAboveModel`
provides the pseudo-coherent scheme and derived-fibre declarations used by the
statement. Its published graph already contains those declarations through the
Sheaf namespace. Keeping direct public imports of the corresponding
`WeilConjectures` modules causes duplicate declaration errors when this restored
module is compiled. The dependency is therefore made public, and the two
redundant direct source imports are removed. The theorem statement and proof
remain unchanged.

## Old

```lean
public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import WeilConjectures.AlgebraicGeometry.DerivedFiberBetti
import Sheaf.AlgebraicGeometry.PseudoCoherentFiberBoundedAboveModel
```

## New

```lean
public import Sheaf.AlgebraicGeometry.PseudoCoherentFiberBoundedAboveModel
```

The Mathlib public imports and the private import of
`WeilConjectures.AlgebraicGeometry.BoundedFiniteFreeFiberModel` remain unchanged.

## Users

`tools/downstream.py` has no current Lean importer of this quarantined module.
Its DAG parents depend on the theorem and will continue to see the same public
statement and all declarations re-exported by the dependency module.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PseudoCoherentFiberFiniteFreeModel | M1 | Public import graph repaired; theorem signature unchanged. |

No target statement or definition changes.

## Status

landed 20261020T235608-L-1194106 2026-10-20 (merge of deliver/M1/Sheaf.AlgebraicGeometry.PseudoCoherentFiberFiniteFreeModel)
