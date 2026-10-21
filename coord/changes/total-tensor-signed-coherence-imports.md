# Sheaf.Algebra.Homology.TotalTensorSignedCoherence import interface

## Reason

The complete proof uses the existing native tensor-summand API rather than the
unproved pure-section constraint theorem. Import the native tensor provider directly
and remove the unused pure-section constraint module. This prunes its proof dependency
from this route. Every existing declaration, definition, signature and visibility stays
unchanged. The private proved helpers use standard elaboration options matching the
native library's shift proofs; those options add no declarations or assumptions.

## Old

```lean
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.RingedTensorComplexConstraints
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.LargeSetSheafification
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.CommGrp_
```

## New

```lean
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Homology.RingedDerivedTensorNative
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Tactic.Ring
```

RingedDerivedTensorNative was already publicly imported by RingedTensorComplexConstraints.
Only the pure-section predicate API from RingedTensorComplexConstraints ceases to be
re-exported. The item's unchanged signatures need none of those predicates.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.TotalTensorSignedCoherence | Q2 | Complete proof; imports native tensor provider directly. |

`tools/downstream.py Sheaf.Algebra.Homology.TotalTensorSignedCoherence` reports zero
current downstream modules. There are no consumer adaptations. DAG parents with
unfinished proofs keep the same theorem and definitions available; their statements
retain exactly the same meaning. No target definition or statement changes.

## Status

landed 20261021T130117-L-2535055 2026-10-21 (merge of deliver/Q2/Sheaf.Algebra.Homology.TotalTensorSignedCoherence)
