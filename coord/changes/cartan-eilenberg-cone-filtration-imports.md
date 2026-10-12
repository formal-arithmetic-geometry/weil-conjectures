# CartanEilenbergConeFiltration imports

## Reason

The HomotopyCategory Acyclic import is unused and is removed from all three
modules, together with the unused DoubleComplexTotal, Filtration, and source-library
Acyclic imports. The two helper modules are imported only for the target proof.
MappingCone is part of the public theorem
signatures, so it is imported explicitly and publicly after removing the
transitive public exposure through Acyclic.

## Old

```lean
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
```

## New

```lean
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
```

All declaration signatures and definitions are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.CartanEilenbergConeFiltration | Q2 | Public MappingCone remains available; unused Acyclic imports are removed; helper imports are proof-only. |
| Sheaf.CategoryTheory.CartanEilenbergAugmentationQuasiIso | unclaimed | Original source compiles against the changed imports; no adaptation required. |

## Status

landed 20261012T202249-L-707746 2026-10-12 (merge of deliver/Q2/Sheaf.CategoryTheory.CartanEilenbergConeFiltration)
