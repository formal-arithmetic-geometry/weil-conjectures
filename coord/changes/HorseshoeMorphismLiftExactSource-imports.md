# HorseshoeMorphismLiftExactSource imports

## Reason
The proved exact-source theorem uses no declaration of HorseshoeMorphismLift.
Its public import was an unused proof-plan dependency. Replace it with the two
Mathlib statement dependencies, and retain Abel as a private proof import.
The repair also imports the existing proved private row-factorization helper with
`import all`, so the duplicated helper is removed without changing dependency visibility.
No existing signature, definition, visibility or target meaning changes.

## Old
```lean
public import Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLift
```

## New
```lean
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Tactic.Abel
import all Sheaf.CategoryTheory.Abelian.HorseshoeDefectFactorization
```

## Users
Ran tools/downstream.py with --direct --uses
exists_horseshoe_morphism_lift_exact_source. The only direct importer is
CartanEilenbergComparisonColumnStep, which imports this module privately.
That module only mentions the theorem in its proof docstring; its theorem is
still open. It already publicly imports Preadditive.Injective.Resolution and
HomologicalComplexAbelian, and privately imports ModelCategory.Injective.
It uses no HorseshoeMorphismLift declaration and requires no adaptation.
The remaining transitive importers obtain no additional public names through
this private import edge. No object or statement meaning can change: the edit
removes theorem availability on one edge, and changes no definition.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource | N1 | Same statement; proof and import pruning only. |
| Sheaf.CategoryTheory.CartanEilenbergComparisonColumnStep | unclaimed | No signature or proof change; removed module supplies no used declaration. |

## Status
landed 20261013T054228-L-446207 2026-10-13 (merge of deliver/N1/Sheaf.CategoryTheory.Abelian.HorseshoeMorphismLiftExactSource)
