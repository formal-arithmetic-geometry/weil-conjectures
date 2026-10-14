# ProjectionFormula import visibility

## Reason

The projection formula module uses `ProjectionMapDualizable` only in proof bodies. `ModuleCat.AB`,
`Etale.Derived.UpperLowerStar`, and `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact` are
redundant because the remaining imports already provide all used declarations. Make the first import
private and remove the three redundant imports. This changes only import visibility; declarations
and definitions are unchanged.

## Old

```lean
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact
```

## New

```lean
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapDualizable
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
```

The former `Sheaf.AlgebraicGeometry.EtaleInverseImageModulesExact` import is removed entirely:
```lean
-- no replacement import
```

## Users

The direct downstream importers are listed below. Their imports and declarations remain valid because
all public declarations they use continue to be reachable through the remaining public imports.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint WeilConjectures WeilConjectures.EtaleCohomology.Purity.Smooth.Coprojection WeilConjectures.FourierTransform.Properties WeilConjectures.SixFunctors.Etale.Derived.Composition WeilConjectures.SixFunctors.Etale.Derived.Exchange WeilConjectures.SixFunctors.Etale.Derived.KernelTransform WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Composition WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Finite WeilConjectures.SixFunctors.Etale.Derived.KernelTransform.Tensor WeilConjectures.SixFunctors.Etale.Derived.Kunneth WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Comparisons WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Relative WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Shriek WeilConjectures.SixFunctors.Etale.Derived.Package WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral WeilConjectures.SixFunctors.Etale.Derived.Stability.ClosedImmersion WeilConjectures.SixFunctors.Etale.Derived.TensorHom WeilConjectures.SixFunctors.ProEtale.Derived.UpperShriekComposition | unclaimed | Existing declarations remain available; no signature or proof change required. |

## Status

landed 20261014T151512-L-1000885 2026-10-14 (merge of deliver/Q1/WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula)
