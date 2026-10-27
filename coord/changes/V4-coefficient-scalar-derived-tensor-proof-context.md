# AlgebraicGeometry.ProEtale.CondensedRing.coefficientScalarDerivedTensorSquare

## Reason

Complete the existing theorem without changing its interface or its underlying constructions.
Keep large ordinary and derived constructions abstract, and make the small
`internalScalarExtension` wrapper available to definitional equality. The new private
`TensorSquare` proposition and its fully proved constructor match monoidal data before
specializing the equation at objects. The comparison aliases have explicit original
bifunctor types, so subsequent composition uses those types consistently.

Profiling isolated costly kernel conversion of the concrete composition equation. The
resulting implementation compiled with profiling enabled in 45.6 seconds, including 32.4
seconds of kernel checking. Development profiling options are removed from the delivery.
The final categorical cancellation explicitly respects both transparency options; the
file's pre-existing global settings are retained.

The existing automatically included section-category parameters stay in the signature.
Their unused-section-variable diagnostic is disabled only for this theorem. This changes
diagnostics, not assumptions. No existing definition body, statement, public import,
exported attribute or registered instance changes.

## Old

```lean
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap internalScalarExtension
  coefficientInternalScalarComplex coefficientSectionScalarPure coefficientSectionScalarTotal
```

There was no diagnostic setting scoped to the theorem.

## New

```lean
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  Mod.extendScalars Mod.comap upperStar internalScalarMonoidal
  Functor.leftDerivedFunctorCompNatIso Functor.leftDerivedTensorComparison
  leftDerivedUpperStarTensor upperStarFromPoint
  coefficientInternalScalarComplex coefficientSectionScalarPure coefficientSectionScalarTotal
```

```lean
set_option linter.unusedSectionVars false in
```

That setting wraps the unchanged theorem and its existing docstring. Its proof contains:

```lean
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
```

The added proof import is private:

```lean
import Sheaf.UpstreamExtra.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
```

The new private declarations are `TensorSquare`, `canonical_tensor_square` and
`tensor_square_from_inv`. They contain no proof holes and are used only by the implementation of this theorem.
The node's proof text records these implementation steps; its dependencies are unchanged.

## Users

`tools/downstream.py Sheaf.Paper.CoefficientScalarDerivedTensorSquare --uses
coefficientScalarDerivedTensorSquare` found the item and the direct declaration user below,
with 586 modules in its transitive import closure at the time of the lookup. The local
settings and private declarations are not exported, and every public declaration retains
its signature. No consumer needs adaptation or a renewed target-statement review.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientScalarDerivedTensorSquare | V4 | Complete its proof. |
| Sheaf.Paper.CoefficientScalarTensorRealization | unclaimed | Unchanged application. |

The clean item and the unchanged direct consumer both passed `lcompile.py`, including
its single-file time gate. The temporary consumer copy was removed after verification.
No consumer source is included or adapted in this delivery.

## Status

landed 20261026T024137-L-641776 2026-10-26 (merge of deliver/V4/Sheaf.Paper.CoefficientScalarDerivedTensorSquare)
