# Sheaf.AlgebraicGeometry.RationalDerivedScalarInvertible imports

## Reason

Remove the unused public import of the right-derived-functor wrapper and two redundant
proof imports after proving the item using only the ordinary unbounded Mathlib derived
localization. Every existing declaration signature, definition, attribute, and visibility
is unchanged. The removed public wrapper is not needed to elaborate any retained public
signature: HasDerivedCategory already supplies the derived localization API, and the
upstream ModuleObject.Basic supplies the module-object category and its instances.
The resulting file compiles and the proved theorem has only the standard three axioms.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtalePointPullback
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.RationalDerivedScalarInvertible | J6 | Compiles with the smaller import interface; all public declaration signatures remain identical. |

There are no current Lean importers of this module, and no current Lean occurrence of
`rationalDerivedScalar_invertible` outside its own file. The DAG parent
`thm-sfb-extend-scalars-localization` still needs this theorem, with exactly the same
statement. It does not use the removed right-derived-functor reexport; its unfinished
proof has no import of the item yet. No consumer adaptation is needed, and no target
statement or definition changes meaning.

## Status

landed 20261021T101153-L-20727 2026-10-21 (merge of deliver/J6/Sheaf.AlgebraicGeometry.RationalDerivedScalarInvertible)
