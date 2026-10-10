/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.UpperLowerStar.Defs

/-!

# Derived upper star and lower star on module objects over `C(-, T)`

Let `T` be a commutative topological ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback and pushforward on the derived categories `D(Mod_{A_X(T)})` of module objects over
`A_X(T) = C(-, T)` are *not* given definitions of their own: as in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`, they are the
*total* derived functors, i.e. the generic derived-functor constructions of the folder
`WeilConjectures.CategoryTheory.DerivedCategory` applied to the underived functors `(f)^*⟦T⟧`
and `(f)_*⟦T⟧` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.UpperLowerStar.Defs`:

| derived functor | notation | meaning |
| --- | --- | --- |
| `Rf_* : D(Mod_{A_X(T)}) ⥤ D(Mod_{A_Y(T)})` | `R((f)_*⟦T⟧)` | `(f)_*⟦T⟧.rightDerivedFunctor` |
| `Rf_* : D⁺(Mod_{A_X(T)}) ⥤ D⁺(Mod_{A_Y(T)})` | `R+((f)_*⟦T⟧)` | `rightDerivedFunctorPlus` |
| `Lf^* : D(Mod_{A_Y(T)}) ⥤ D(Mod_{A_X(T)})` | `L((f)^*⟦T⟧)` | `(f)^*⟦T⟧.leftDerivedFunctor` |

The derived pushforward is computed on K-injective resolutions in `Mod_{A_X(T)}`, and the
derived pullback is the total left derived functor of `f^* = A_X(T) ⊗_{f^* A_Y(T)} f^*(-)`,
computed on K-flat resolutions in `Mod_{A_Y(T)}`, that is
```
Lf^* M = A_X(T) ⊗ᴸ_{f^* A_Y(T)} f^* M,
```
the derived extension of scalars along `α_f` of the exact pullback `f^* M`; this is the
pullback of Bhatt–Scholze, Remark 6.8.15, for `𝒪_E`- and `E`-coefficients. In contrast with the
finite-coefficient case, `f^*` on module objects is *not* exact (the extension of scalars along
`α_f` is only right exact), so `Lf^*` is not the levelwise functor: this is exactly the situation
the K-flat left derivability structure of
`WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Defs` is designed for.

The two displayed formulas are theorems about the total derived functors, not definitions:

* `ProEtale.ContinuousMapRing.rightDerivedLowerStarIso`:
  `R((f)_*⟦T⟧) ≅ R(mapMod(f_*)) ⋙ D(Res_{η_f})`. The restriction of scalars along
  `η_f : A_Y(T) ⟶ f_* A_X(T)` is exact, so right deriving the composite
  `(f)_*⟦T⟧ = mapMod(f_*) ⋙ Res_{η_f}` amounts to right deriving `mapMod(f_*)` and restricting
  scalars levelwise (`Functor.rightDerivedFunctorCompMapDerivedCategoryIso`).
* `ProEtale.ContinuousMapRing.leftDerivedUpperStarIso`:
  `L((f)^*⟦T⟧) ≅ D(mapMod(f^*)) ⋙ L(Ext_{α_f})`. The exact functor `mapMod(f^*)` preserves
  K-flat complexes, so left deriving the composite `(f)^*⟦T⟧ = mapMod(f^*) ⋙ Ext_{α_f}` amounts
  to applying `mapMod(f^*)` levelwise and left deriving the extension of scalars, both being
  computed on the same K-flat resolution in `Mod_{A_Y(T)}`
  (`Functor.leftDerivedFunctorCompMapDerivedCategoryIso`).

## Main results

- `ProEtale.ContinuousMapRing.derivedUpperStarLowerStarAdjunction`: the derived adjunction
  `L((f)^*⟦T⟧) ⊣ R((f)_*⟦T⟧)`, induced by the adjunction `f^* ⊣ f_*` on module objects.

- `ProEtale.ContinuousMapRing.rightDerivedLowerStarIso` and
  `ProEtale.ContinuousMapRing.leftDerivedUpperStarIso`: the computations of `Rf_*` and `Lf^*`
  described above.

There is no bounded below derived adjunction in general, `f^*` on module objects not being
exact; for an open immersion see the file
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.Derived.OpenImmersionLowerShriek`
of this folder.

## Sorried input

- `ProEtale.ContinuousMapRing.preservesKFlatComplexes_mapMod_upperStar`: `mapMod(f^*)` sends
  K-flat complexes of `A_Y(T)`-modules to K-flat complexes of `f^* A_Y(T)`-modules. Indeed
  `f^*` is strong monoidal, exact and commutes with colimits, so it commutes with the relative
  tensor product of complexes of module objects and preserves acyclicity. From it follows that
  the pullback `(f)^*⟦T⟧ = mapMod(f^*) ⋙ Ext_{α_f}` on module objects preserves
  quasi-isomorphisms between K-flat complexes
  (`ProEtale.ContinuousMapRing.preservesKFlatQuasiIso_upperStar`), which is the functor-specific
  input of the K-flat machinery making `L((f)^*⟦T⟧)` meaningful; the other ingredient is that
  extension of scalars preserves quasi-isomorphisms between K-flat complexes
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

/-! ### The derived pushforward -/

section DerivedLowerStar

/-- The total right derived functor `Rf_* : D(Mod_{A_X(T)}) ⥤ D(Mod_{A_Y(T)})` of the
pushforward `f_*` on module objects over `C(-, T)`, on the unbounded derived categories,
computed on K-injective resolutions.

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

/-- The derived pushforward on module objects is the total right derived functor of
`mapMod(f_*) : Mod_{A_X(T)} ⥤ Mod_{f_* A_X(T)}` followed by the levelwise restriction of scalars
along `η_f : A_Y(T) ⟶ f_* A_X(T)`: the restriction of scalars is exact, so right deriving the
composite `(f)_*⟦T⟧ = mapMod(f_*) ⋙ Res_{η_f}` amounts to right deriving `mapMod(f_*)` and
restricting scalars levelwise. -/
noncomputable def rightDerivedLowerStarIso :
    R((f)_*⟦T⟧) ≅
      R((f)_*[Ab.{u + 1}].mapMod (R := continuousMapRingObj T X)) ⋙
        D(Mod.comap (continuousMapPushforwardHom T f)) :=
  Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    ((f)_*[Ab.{u + 1}].mapMod (R := continuousMapRingObj T X))
    (Mod.comap (continuousMapPushforwardHom T f))

end DerivedLowerStar

/-! ### The derived pullback -/

section DerivedUpperStar

instance preservesHomology_mapMod_upperStar :
    ((f)^*[Ab.{u + 1}].mapMod (R := continuousMapRingObj T Y)).PreservesHomology := {}

/-- The pullback `mapMod(f^*) : Mod_{A_Y(T)} ⥤ Mod_{f^* A_Y(T)}` sends K-flat complexes to
K-flat complexes. See the module docstring for the argument. -/
instance preservesKFlatComplexes_mapMod_upperStar :
    ((f)^*[Ab.{u + 1}].mapMod (R := continuousMapRingObj T Y)).PreservesKFlatComplexes := sorry

/-- The pullback `(f)^*⟦T⟧ = mapMod(f^*) ⋙ Ext_{α_f}` on module objects over `C(-, T)` preserves
quasi-isomorphisms between K-flat complexes: `mapMod(f^*)` is exact and preserves K-flat
complexes, and the extension of scalars preserves quasi-isomorphisms between K-flat
complexes. This is the functor-specific input of the K-flat left derivability structure. -/
instance preservesKFlatQuasiIso_upperStar : (f)^*⟦T⟧.PreservesKFlatQuasiIso :=
  Functor.preservesKFlatQuasiIso_comp
    ((f)^*[Ab.{u + 1}].mapMod (R := continuousMapRingObj T Y))
    (Mod.extendScalars (continuousMapPullbackHom T f))

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

/-- The derived pullback on module objects is the levelwise pullback
`D(mapMod(f^*)) : D(Mod_{A_Y(T)}) ⥤ D(Mod_{f^* A_Y(T)})` followed by the derived extension of
scalars `A_X(T) ⊗ᴸ_{f^* A_Y(T)} -` along `α_f`: `mapMod(f^*)` is exact and preserves K-flat
complexes, so left deriving the composite `(f)^*⟦T⟧ = mapMod(f^*) ⋙ Ext_{α_f}` amounts to
applying `mapMod(f^*)` levelwise and left deriving the extension of scalars. -/
noncomputable def leftDerivedUpperStarIso :
    L((f)^*⟦T⟧) ≅
      D((f)^*[Ab.{u + 1}].mapMod (R := continuousMapRingObj T Y)) ⋙
        L(Mod.extendScalars (continuousMapPullbackHom T f)) :=
  Functor.leftDerivedFunctorCompMapDerivedCategoryIso
    ((f)^*[Ab.{u + 1}].mapMod (R := continuousMapRingObj T Y))
    (Mod.extendScalars (continuousMapPullbackHom T f))

end DerivedUpperStar

/-! ### The derived adjunction `Lf^* ⊣ Rf_*` -/

section Adjunction

/-- The derived adjunction `Lf^* ⊣ Rf_*` between the total derived functors of the pullback
and the pushforward on module objects over `C(-, T)`, induced by the adjunction `f^* ⊣ f_*` of
`ProEtale.ContinuousMapRing.upperStarLowerStarAdjunction`: the left adjoint is derived via the
K-flat left derivability structure on `D(Mod_{A_Y(T)})` and the right adjoint via the
K-injective right derivability structure on `D(Mod_{A_X(T)})`. -/
noncomputable def derivedUpperStarLowerStarAdjunction : L((f)^*⟦T⟧) ⊣ R((f)_*⟦T⟧) :=
  (upperStarLowerStarAdjunction T f).derivedAdjunction

instance : L((f)^*⟦T⟧).IsLeftAdjoint := (derivedUpperStarLowerStarAdjunction T f).isLeftAdjoint

instance : R((f)_*⟦T⟧).IsRightAdjoint := (derivedUpperStarLowerStarAdjunction T f).isRightAdjoint

end Adjunction

end AlgebraicGeometry.ProEtale.ContinuousMapRing
