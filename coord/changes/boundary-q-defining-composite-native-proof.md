# Sheaf.Paper.BoundaryQDefiningCompositeComparison imports and proof context

## Reason

The complete proof uses the existing native derived comparison and its K-flat counit
normalization. Four public imports and two proof imports are unnecessary for the
statement, definitions, and proof. Removing them prunes the unused ringed-presentation
route. The proof adds only proved private helpers and their variable/open context.
Existing public declaration signatures and all definition bodies remain byte-identical.

## Old

The original imports, verbatim:

```lean
public import Sheaf.Paper.BoundaryExceptionalComparisonData
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteModules
public import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.SixFunctors.RingedDerivedMonoidalComparisons
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
```

The original top-level proof context, verbatim:

```lean
universe u v

open CategoryTheory CategoryTheory.Limits
```

## New

The replacement imports, verbatim:

```lean
public import Sheaf.Paper.BoundaryExceptionalComparisonData
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.CategoryTheory.Monoidal.Braided.Adjunction
```

The proof context begins with the following; the remaining added context is used only
by the proved private helper declarations in the same module:

```lean
universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
```

The two local irreducibility attributes affect elaboration of the private diagram
proof only. No global instance, public declaration, notation, or definition is added
or changed. The previously public comparison/pullback interface is still available
through the kept `BoundaryExceptionalComparisonData` import. Removed imports' own
modules and declarations remain in the library.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.BoundaryQDefiningCompositeComparison | Q7 | One theorem proof completed; imports pruned; private proof helpers added. |

`tools/downstream.py Sheaf.Paper.BoundaryQDefiningCompositeComparison --uses
boundaryDefiningSourceIso boundaryDefiningTargetIso boundaryEtaleDefiningComposite
BoundaryDefiningCompositeComparison boundary_q_defining_composite_comparison`
reported zero downstream modules on 2026-10-21; each name is currently mentioned only
in the item itself. No consumer adaptation is required. This is not a withdrawal:
the DAG's unfinished parent still needs the item, and its Lean attachment and all
public declarations are preserved. No target statement or definition used by a
target changes meaning.

## Status

landed 20261021T154048-L-2781595 2026-10-21 (merge of deliver/Q7/Sheaf.Paper.BoundaryQDefiningCompositeComparison)
