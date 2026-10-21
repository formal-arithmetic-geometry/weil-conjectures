# Sheaf.SixFunctors.FiniteProperClassicalTruncation public imports

## Reason

The original statement module publicly reexported four broad support modules that its
statement does not need. The completed proof uses the canonical total derived direct image
and Mathlib's fibre and good-truncation APIs. Replace the broad public imports with the
particular Mathlib imports needed by the unchanged statement, and import the additional
proof dependencies privately. This changes the module's reexports; it changes no existing
public declaration's name, signature, universes, visibility, or mathematical meaning.

## Old

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
```

## New

```lean
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Sheaf.SixFunctors.ClassicalDefinition
public import Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage
```

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.FiniteProperClassicalTruncation
--uses finiteProper_classical_truncation` reports zero downstream Lean modules. The only
textual declaration use in that scan is the item's own declaration. Therefore there are no
existing consumers to adapt. The DAG attachment is preserved, including statement
references by unfinished parents; no module or declaration is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.FiniteProperClassicalTruncation | S9 | Removes four unused public reexports, adds the specific Mathlib statement imports, and proves the unchanged theorem. |

## Status

landed 20261021T120525-L-3906282 2026-10-21 (merge of deliver/S9/Sheaf.SixFunctors.FiniteProperClassicalTruncation)
