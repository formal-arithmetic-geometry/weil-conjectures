# EtaleFieldGaloisClassification imports

## Reason

Expose only the modules needed by the unchanged theorem signature. The infinite
Galois correspondence is used only in the proof. Remove redundant direct imports.
No definition or declaration signature changes, so no target meaning changes.

## Old

```lean
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.Topology.Algebra.Group.Basic
import Sheaf.FieldTheory.OpenSubgroupFixedField
```

## New

```lean
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.Infinite
import Sheaf.FieldTheory.OpenSubgroupFixedField
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.FieldTheory.EtaleFieldGaloisClassification | T1 | Same theorem signature; clean compilation and standard axioms after import cleanup. |
| Sheaf.AlgebraicGeometry.EtaleFieldPointFunctor | P2 | Direct importer through a plain proof import; original module compiles against the delivered classification without adaptation. |
| Sheaf.AlgebraicGeometry.EtaleFieldPointFunctorEssSurj | E2 | Direct importer through a plain proof import; original module compiles against the delivered classification without adaptation. |

The two direct importers are EtaleFieldPointFunctor and EtaleFieldPointFunctorEssSurj; EtaleFieldGsets imports the latter indirectly. The
classification remains available with precisely its original statement, and
SeparableClosure and Group.Basic remain public transitive imports of the retained
statement modules. Only proof-specific infinite-Galois results stop being re-exported.

## Status

landed 20261012T135317-L-1692755 2026-10-12 (merge of deliver/T1/Sheaf.FieldTheory.EtaleFieldGaloisClassification)
