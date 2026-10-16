# AlgebraicGeometry.Etale.finite_range_exchange_comparison: unused imports

## Reason

Second reading found three public imports that supply no declaration used by the
statement or proof: ChosenCartesianSquare, DerivedCategories, and
HypercohomologyFiltrations. The statement uses Mathlib's IsPullback, the existing
DerivedCategory.Plus, and the truncation data from TruncationExchangeCouple.
Remove the unused imports. No declaration, definition, hypothesis, or conclusion
changes. The separate proof-only SpectralSequencePageInduction import is also
removed because page comparison is proved locally. The final import block also
includes the proof-only DerivedCoupleFunctoriality and ExactFunctorHalfPlane imports documented in
finite-range-comparison-reuse-functoriality.md.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.AlgebraicGeometry.TruncationExchangeCouple
public import Sheaf.AlgebraicGeometry.HypercohomologyFiltrations
public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.ExactCoupleMorphism
import Sheaf.CategoryTheory.SpectralSequencePageInduction
import Sheaf.CategoryTheory.FiniteFiltrationInduction
import Sheaf.AlgebraicGeometry.TruncationExchangeAbutment
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
```

## New

```lean
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import Sheaf.AlgebraicGeometry.TruncationExchangeCouple
public import Sheaf.CategoryTheory.ExactCoupleConvergence
import Sheaf.CategoryTheory.ExactCoupleMorphism
import Sheaf.CategoryTheory.DerivedCoupleFunctoriality
import Sheaf.CategoryTheory.ExactFunctorHalfPlane
import Sheaf.CategoryTheory.FiniteFiltrationInduction
import Sheaf.AlgebraicGeometry.TruncationExchangeAbutment
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
```

## Users

Rechecked against the current shared repository on 2026-10-16 using
`python3 tools/downstream.py Sheaf.AlgebraicGeometry.FiniteRangeComparison --uses
AlgebraicGeometry.Etale.finite_range_exchange_comparison`:
zero downstream modules; the only occurrence of the theorem is its declaration
in the item itself. The earlier list of five importers predates the upstream
sync and is superseded by this source-graph check.

| module | group holding it | effect |
|---|---|---|

No downstream adaptation is required. No target statement or definition changes.
This module is currently outside the targets' import closure, so closing its
hole does not claim a decrease in that closure's sorry count.

## Status

landed 20261016T075723-L-1295295 2026-10-16 (merge of deliver/C3/Sheaf.AlgebraicGeometry.FiniteRangeComparison)
