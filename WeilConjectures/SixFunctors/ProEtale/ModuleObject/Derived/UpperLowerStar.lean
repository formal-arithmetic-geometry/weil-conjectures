/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# Derived upper star and lower star on module objects over `C(-, T)`

Let `T` be a commutative topological ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback and pushforward on the derived categories `D(Mod_{A_X(T)})` of module objects over
`A_X(T) = C(-, T)` are *not* given definitions of their own: as in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`, they are the
generic derived-functor constructions of the folder
`WeilConjectures.CategoryTheory.DerivedCategory` applied to the underived functors `(f)^*⟦T⟧`
and `(f)_*⟦T⟧` of `WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:

| derived functor | notation | meaning |
| --- | --- | --- |
| `Rf_* : D(Mod_{A_X(T)}) ⥤ D(Mod_{A_Y(T)})` | `R((f)_*⟦T⟧)` | `(f)_*⟦T⟧.rightDerivedFunctor` |
| `Rf_* : D⁺(Mod_{A_X(T)}) ⥤ D⁺(Mod_{A_Y(T)})` | `R+((f)_*⟦T⟧)` | `rightDerivedFunctorPlus` |
| `Lf^* : D(Mod_{A_Y(T)}) ⥤ D(Mod_{A_X(T)})` | `L((f)^*⟦T⟧)` | `(f)^*⟦T⟧.leftDerivedFunctor` |

The derived pullback is the total left derived functor of `f^* = A_X(T) ⊗_{f^* A_Y(T)} f^*(-)`
computed on K-flat resolutions, that is
```
Lf^* M = A_X(T) ⊗ᴸ_{f^* A_Y(T)} f^* M,
```
the derived extension of scalars along `α_f` of the exact pullback `f^* M`; this is the
pullback of Bhatt–Scholze, Remark 6.8.15, for `𝒪_E`- and `E`-coefficients. In contrast with the
finite-coefficient case, `f^*` on module objects is *not* exact (the extension of scalars along
`α_f` is only right exact), so `Lf^*` is not the levelwise functor: this is exactly the situation
the K-flat left derivability structure of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs` is designed for.

## Main results

- `ProEtale.ContinuousMapRing.derivedUpperStarLowerStarAdjunction`: the derived adjunction
  `L((f)^*⟦T⟧) ⊣ R((f)_*⟦T⟧)`, induced by the adjunction `f^* ⊣ f_*` on module objects.

## Sorried input

- `ProEtale.ContinuousMapRing.preservesKFlatQuasiIso_upperStar`: the pullback `f^*` on module
  objects preserves quasi-isomorphisms between K-flat complexes, which is the functor-specific
  input of the K-flat machinery. Indeed `f^* = mapMod(f^*)` followed by extension of scalars
  along `α_f`; the exact functor `mapMod(f^*)` sends K-flat complexes of `A_Y(T)`-modules to
  K-flat complexes of `f^* A_Y(T)`-modules, since `f^*` is strong monoidal and commutes with
  colimits, and extension of scalars preserves quasi-isomorphisms between K-flat complexes
  (`Mod.preservesKFlatQuasiIso`, itself sorried in
  `WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars`).

The remaining sorries are those of the module-object formalism
(`WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`,
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`), of the pro-étale
sheaf categories (`AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf`) and of `Ab`
(`AddCommGrpCat.hasFunctorialFlatResolution`).

-/

@[expose] public section

universe u

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

section DerivedLowerStar

/-- The total right derived functor `Rf_* : D(Mod_{A_X(T)}) ⥤ D(Mod_{A_Y(T)})` of the
pushforward `f_*` on module objects over `C(-, T)`, on the unbounded derived categories.

It is not a definition of its own: it is the generic `Functor.rightDerivedFunctor`, written
`R(-)`, applied to the underived pushforward `(f)_*⟦T⟧`. -/
noncomputable example :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (continuousMapRingObj T X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (continuousMapRingObj T Y)) :=
  R((f)_*⟦T⟧)

/-- The right derived functor `Rf_* : D⁺(Mod_{A_X(T)}) ⥤ D⁺(Mod_{A_Y(T)})` of the pushforward
`f_*` on module objects, on the *bounded below* derived categories: the generic
`Functor.rightDerivedFunctorPlus`, written `R+(-)`, applied to `(f)_*⟦T⟧`. -/
noncomputable example :
    DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousMapRingObj T X)) ⥤
      DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (continuousMapRingObj T Y)) :=
  R+((f)_*⟦T⟧)

end DerivedLowerStar

section DerivedUpperStar

/-- The pullback `f^*` on module objects over `C(-, T)` preserves quasi-isomorphisms between
K-flat complexes. See the module docstring for the argument. -/
instance preservesKFlatQuasiIso_upperStar : (f)^*⟦T⟧.PreservesKFlatQuasiIso := sorry

/-- The total left derived functor `Lf^* : D(Mod_{A_Y(T)}) ⥤ D(Mod_{A_X(T)})` of the pullback
`f^*` on module objects over `C(-, T)`, on the unbounded derived categories, computed on K-flat
resolutions: `Lf^* M = A_X(T) ⊗ᴸ_{f^* A_Y(T)} f^* M`.

It is not a definition of its own: it is the generic `Functor.leftDerivedFunctor`, written
`L(-)`, applied to the underived pullback `(f)^*⟦T⟧`. -/
noncomputable example :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (continuousMapRingObj T Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (continuousMapRingObj T X)) :=
  L((f)^*⟦T⟧)

/-- The derived adjunction `Lf^* ⊣ Rf_*` between the total derived functors of the pullback
and the pushforward on module objects over `C(-, T)`, induced by the adjunction `f^* ⊣ f_*` of
`ProEtale.ContinuousMapRing.upperStarLowerStarAdjunction`. -/
noncomputable def derivedUpperStarLowerStarAdjunction : L((f)^*⟦T⟧) ⊣ R((f)_*⟦T⟧) :=
  (upperStarLowerStarAdjunction T f).derivedAdjunction

instance : L((f)^*⟦T⟧).IsLeftAdjoint := (derivedUpperStarLowerStarAdjunction T f).isLeftAdjoint

instance : R((f)_*⟦T⟧).IsRightAdjoint := (derivedUpperStarLowerStarAdjunction T f).isRightAdjoint

end DerivedUpperStar

end AlgebraicGeometry.ProEtale.ContinuousMapRing
