# AlgebraicGeometry.Etale.EtaleChartCompactSupportNormalization

## Reason

The completed proof does not use the closed-support triangle, quasi-finite
proper-support package, or source-open composition theorem. Their public
imports were unused by the statement and definition as well. Remove those
three public imports, and redundant private imports, so that this module's
interface and DAG record its actual requirements. The theorem and definition
signatures and the definition body remain verbatim.

## Old

```lean
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Sheaf.AlgebraicGeometry.OpenSourceComposition
public import Sheaf.AlgebraicGeometry.QuasiFiniteCompactSupportExact
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Finite.Exact
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.NumberTheory.Padics.PadicNumbers
import Sheaf.AlgebraicGeometry.ProperSupportSheafComposition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.Compactification.Dense
```

## New

```lean
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Finite.Exact
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleChartCompactSupportNormalization | Q6 | Complete the proof; remove unused imports; unchanged declarations. |

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.EtaleChartCompactSupportNormalization
--uses EtaleChartCompactSupportNormalization` reports zero downstream modules,
and only this module as a declaration user. The same check for the theorem
name reports zero downstream modules and only this module. There are no consumer
adaptations. DAG parents with unfinished proofs continue to use the unchanged
node and declaration; neither is withdrawn. No target statement is changed.

## Status

landed 20261023T151930-L-423880 2026-10-23 (merge of deliver/Q6/Sheaf.AlgebraicGeometry.EtaleChartCompactSupportNormalization)
