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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.UpperLowerStar.Defs

/-!

# Derived upper star and lower star on module objects over `ℚ̄_ℓ`

Let `ℓ` be a prime and `f : X ⟶ Y` a morphism of schemes. The derived
pullback and pushforward on the derived categories `D(Mod_{ℚ̄_ℓ,X})` of module objects over
`ℚ̄_ℓ,X` are *not* given definitions of their own: as in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`, they are the
*total* derived functors, i.e. the generic derived-functor constructions of the folder
`WeilConjectures.CategoryTheory.DerivedCategory` applied to the underived functors `(f)^*⟦ℚ̄_ℓ⟧`
and `(f)_*⟦ℚ̄_ℓ⟧` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.UpperLowerStar.Defs`:

| derived functor | notation | meaning |
| --- | --- | --- |
| `Rf_* : D(Mod_{ℚ̄_ℓ,X}) ⥤ D(Mod_{ℚ̄_ℓ,Y})` | `R((f)_*⟦ℚ̄_ℓ⟧)` | `rightDerivedFunctor` |
| `Rf_* : D⁺(Mod_{ℚ̄_ℓ,X}) ⥤ D⁺(Mod_{ℚ̄_ℓ,Y})` | `R+((f)_*⟦ℚ̄_ℓ⟧)` | `rightDerivedFunctorPlus` |
| `Lf^* : D(Mod_{ℚ̄_ℓ,Y}) ⥤ D(Mod_{ℚ̄_ℓ,X})` | `L((f)^*⟦ℚ̄_ℓ⟧)` | `leftDerivedFunctor` |
| `f^* : D(Mod_{ℚ̄_ℓ,Y}) ⥤ D(Mod_{ℚ̄_ℓ,X})` | `D((f)^*⟦ℚ̄_ℓ⟧)` | `mapDerivedCategory` |
| `f^* : D⁺(Mod_{ℚ̄_ℓ,Y}) ⥤ D⁺(Mod_{ℚ̄_ℓ,X})` | `D+((f)^*⟦ℚ̄_ℓ⟧)` | `mapDerivedCategoryPlus` |

The derived pushforward is computed on K-injective resolutions in `Mod_{ℚ̄_ℓ,X}`, and the
derived pullback is the total left derived functor of `f^* = ℚ̄_ℓ,X ⊗_{f^* ℚ̄_ℓ,Y} f^*(-)`,
computed on K-flat resolutions in `Mod_{ℚ̄_ℓ,Y}`, that is
```
Lf^* M = ℚ̄_ℓ,X ⊗ᴸ_{f^* ℚ̄_ℓ,Y} f^* M,
```
the derived extension of scalars along `α_f` of the exact pullback `f^* M`; this is the
pullback of Bhatt–Scholze, Section 6.8, for `ℚ̄_ℓ`-coefficients. The pullback `f^*` on module
objects is *assumed* to be exact (`ProEtale.PadicAlgClRing.preservesFiniteLimits_upperStar`, see
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.UpperLowerStar.Defs`), so, as for
étale sheaves, `Lf^*` is canonically the levelwise functor `D((f)^*⟦ℚ̄_ℓ⟧)`
(`ProEtale.PadicAlgClRing.leftDerivedUpperStarIsoMapDerivedCategory`), and on the bounded below
derived categories the pullback is the levelwise functor `D+((f)^*⟦ℚ̄_ℓ⟧)`, left adjoint to
`R+((f)_*⟦ℚ̄_ℓ⟧)` (`ProEtale.PadicAlgClRing.derivedUpperStarLowerStarAdjunctionPlus`).

The two displayed formulas are theorems about the total derived functors, not definitions:

* `ProEtale.PadicAlgClRing.rightDerivedLowerStarIso`:
  `R((f)_*⟦ℚ̄_ℓ⟧) ≅ R(mapMod(f_*)) ⋙ D(Res_{η_f})`. The restriction of scalars along
  `η_f : ℚ̄_ℓ,Y ⟶ f_* ℚ̄_ℓ,X` is exact, so right deriving the composite
  `(f)_*⟦ℚ̄_ℓ⟧ = mapMod(f_*) ⋙ Res_{η_f}` amounts to right deriving `mapMod(f_*)` and restricting
  scalars levelwise (`Functor.rightDerivedFunctorCompMapDerivedCategoryIso`).
* `ProEtale.PadicAlgClRing.leftDerivedUpperStarIso`:
  `L((f)^*⟦ℚ̄_ℓ⟧) ≅ D(mapMod(f^*)) ⋙ L(Ext_{α_f})`. The exact functor `mapMod(f^*)` preserves
  K-flat complexes, so left deriving the composite `(f)^*⟦ℚ̄_ℓ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` amounts
  to applying `mapMod(f^*)` levelwise and left deriving the extension of scalars, both being
  computed on the same K-flat resolution in `Mod_{ℚ̄_ℓ,Y}`
  (`Functor.leftDerivedFunctorCompMapDerivedCategoryIso`).

## Main results

- `ProEtale.PadicAlgClRing.derivedUpperStarLowerStarAdjunction`: the derived adjunction
  `L((f)^*⟦ℚ̄_ℓ⟧) ⊣ R((f)_*⟦ℚ̄_ℓ⟧)`, induced by the adjunction `f^* ⊣ f_*` on module objects, and
  `ProEtale.PadicAlgClRing.derivedUpperStarLowerStarAdjunctionPlus`: its bounded below version
  `D+((f)^*⟦ℚ̄_ℓ⟧) ⊣ R+((f)_*⟦ℚ̄_ℓ⟧)`.

- `ProEtale.PadicAlgClRing.leftDerivedUpperStarIsoMapDerivedCategory`: the derived pullback
  `L((f)^*⟦ℚ̄_ℓ⟧)` is the levelwise functor `D((f)^*⟦ℚ̄_ℓ⟧)`.

- `ProEtale.PadicAlgClRing.leftDerivedUpperStarComp`: the composition isomorphism
  `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, obtained from the underived
  `ProEtale.PadicAlgClRing.upperStarComp` through the levelwise functors.

- `ProEtale.PadicAlgClRing.rightDerivedLowerStarIso` and
  `ProEtale.PadicAlgClRing.leftDerivedUpperStarIso`: the computations of `Rf_*` and `Lf^*`
  described above.

## Sorried input

- `ProEtale.PadicAlgClRing.preservesKFlatComplexes_mapMod_upperStar`: `mapMod(f^*)` sends
  K-flat complexes of `ℚ̄_ℓ,Y`-modules to K-flat complexes of `f^* ℚ̄_ℓ,Y`-modules. Indeed
  `f^*` is strong monoidal, exact and commutes with colimits, so it commutes with the relative
  tensor product of complexes of module objects and preserves acyclicity. From it follows that
  the pullback `(f)^*⟦ℚ̄_ℓ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` on module objects preserves
  quasi-isomorphisms between K-flat complexes
  (`ProEtale.PadicAlgClRing.preservesKFlatQuasiIso_upperStar`), which is the functor-specific
  input of the K-flat machinery making `L((f)^*⟦ℚ̄_ℓ⟧)` meaningful; the other ingredient is that
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

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The derived pushforward -/

section DerivedLowerStar

/-- The total right derived functor `Rf_* : D(Mod_{ℚ̄_ℓ,X}) ⥤ D(Mod_{ℚ̄_ℓ,Y})` of the
pushforward `f_*` on module objects over `ℚ̄_ℓ`, on the unbounded derived categories,
computed on K-injective resolutions.

It is not a definition of its own: it is the generic `Functor.rightDerivedFunctor`, written
`R(-)`, applied to the underived pushforward `(f)_*⟦ℚ̄_ℓ⟧`. -/
noncomputable example :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (padicAlgClSheaf Y ℓ)) :=
  R((f)_*⟦ℚ̄_ℓ⟧)

/-- The right derived functor `Rf_* : D⁺(Mod_{ℚ̄_ℓ,X}) ⥤ D⁺(Mod_{ℚ̄_ℓ,Y})` of the pushforward
`f_*` on module objects, on the *bounded below* derived categories: the generic
`Functor.rightDerivedFunctorPlus`, written `R+(-)`, applied to `(f)_*⟦ℚ̄_ℓ⟧`. -/
noncomputable example :
    DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (padicAlgClSheaf X ℓ)) ⥤
      DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (padicAlgClSheaf Y ℓ)) :=
  R+((f)_*⟦ℚ̄_ℓ⟧)

/-- The derived pushforward on module objects is the total right derived functor of
`mapMod(f_*) : Mod_{ℚ̄_ℓ,X} ⥤ Mod_{f_* ℚ̄_ℓ,X}` followed by the levelwise restriction of scalars
along `η_f : ℚ̄_ℓ,Y ⟶ f_* ℚ̄_ℓ,X`: the restriction of scalars is exact, so right deriving the
composite `(f)_*⟦ℚ̄_ℓ⟧ = mapMod(f_*) ⋙ Res_{η_f}` amounts to right deriving `mapMod(f_*)` and
restricting scalars levelwise. -/
noncomputable def rightDerivedLowerStarIso :
    R((f)_*⟦ℚ̄_ℓ⟧) ≅
      R((f)_*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf X ℓ)) ⋙
        D(Mod.comap (padicAlgClPushforwardHom ℓ f)) :=
  Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    ((f)_*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf X ℓ))
    (Mod.comap (padicAlgClPushforwardHom ℓ f))

end DerivedLowerStar

/-! ### The derived pullback -/

section DerivedUpperStar

instance preservesHomology_mapMod_upperStar :
    ((f)^*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf Y ℓ)).PreservesHomology := {}

/-- The pullback `mapMod(f^*) : Mod_{ℚ̄_ℓ,Y} ⥤ Mod_{f^* ℚ̄_ℓ,Y}` sends K-flat complexes to
K-flat complexes. See the module docstring for the argument. -/
instance preservesKFlatComplexes_mapMod_upperStar :
    ((f)^*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf Y ℓ)).PreservesKFlatComplexes := sorry

/-- The pullback `(f)^*⟦ℚ̄_ℓ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` on module objects over `ℚ̄_ℓ` preserves
quasi-isomorphisms between K-flat complexes: `mapMod(f^*)` is exact and preserves K-flat
complexes, and the extension of scalars preserves quasi-isomorphisms between K-flat
complexes. This is the functor-specific input of the K-flat left derivability structure. -/
instance preservesKFlatQuasiIso_upperStar : (f)^*⟦ℚ̄_ℓ⟧.PreservesKFlatQuasiIso :=
  Functor.preservesKFlatQuasiIso_comp
    ((f)^*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf Y ℓ))
    (Mod.extendScalars (padicAlgClPullbackHom ℓ f))

/-- The total left derived functor `Lf^* : D(Mod_{ℚ̄_ℓ,Y}) ⥤ D(Mod_{ℚ̄_ℓ,X})` of the pullback
`f^*` on module objects over `ℚ̄_ℓ`, on the unbounded derived categories, computed on K-flat
resolutions: `Lf^* M = ℚ̄_ℓ,X ⊗ᴸ_{f^* ℚ̄_ℓ,Y} f^* M`.

It is not a definition of its own: it is the generic `Functor.leftDerivedFunctor`, written
`L(-)`, applied to the underived pullback `(f)^*⟦ℚ̄_ℓ⟧`. -/
noncomputable example :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (padicAlgClSheaf Y ℓ)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (padicAlgClSheaf X ℓ)) :=
  L((f)^*⟦ℚ̄_ℓ⟧)

/-- The derived pullback on module objects is the levelwise pullback
`D(mapMod(f^*)) : D(Mod_{ℚ̄_ℓ,Y}) ⥤ D(Mod_{f^* ℚ̄_ℓ,Y})` followed by the derived extension of
scalars `ℚ̄_ℓ,X ⊗ᴸ_{f^* ℚ̄_ℓ,Y} -` along `α_f`: `mapMod(f^*)` is exact and preserves K-flat
complexes, so left deriving the composite `(f)^*⟦ℚ̄_ℓ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` amounts to
applying `mapMod(f^*)` levelwise and left deriving the extension of scalars. -/
noncomputable def leftDerivedUpperStarIso :
    L((f)^*⟦ℚ̄_ℓ⟧) ≅
      D((f)^*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf Y ℓ)) ⋙
        L(Mod.extendScalars (padicAlgClPullbackHom ℓ f)) :=
  Functor.leftDerivedFunctorCompMapDerivedCategoryIso
    ((f)^*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf Y ℓ))
    (Mod.extendScalars (padicAlgClPullbackHom ℓ f))

/-- The derived pullback on module objects is the levelwise functor: since `f^*` on module
objects is exact (`ProEtale.PadicAlgClRing.preservesFiniteLimits_upperStar`), its total left
derived functor `L((f)^*⟦ℚ̄_ℓ⟧)`, computed via K-flat resolutions, is canonically isomorphic to
the functor `D((f)^*⟦ℚ̄_ℓ⟧)` induced by applying `f^*` levelwise. This is
`Functor.leftDerivedFunctorIsoMapDerivedCategory` at `f^*`. -/
noncomputable def leftDerivedUpperStarIsoMapDerivedCategory :
    L((f)^*⟦ℚ̄_ℓ⟧) ≅ D((f)^*⟦ℚ̄_ℓ⟧) :=
  (f)^*⟦ℚ̄_ℓ⟧.leftDerivedFunctorIsoMapDerivedCategory

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of derived pullbacks on module
objects over `ℚ̄_ℓ`, obtained from the underived composition isomorphism
`ProEtale.PadicAlgClRing.upperStarComp` and the compatibility of left derivation with
`mapDerivedCategory` for exact functors. -/
noncomputable def leftDerivedUpperStarComp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    L((f ≫ g)^*⟦ℚ̄_ℓ⟧) ≅ L((g)^*⟦ℚ̄_ℓ⟧) ⋙ L((f)^*⟦ℚ̄_ℓ⟧) :=
  Functor.leftDerivedFunctorNatIso _ (upperStarComp ℓ f g) ≪≫
    Functor.leftDerivedFunctorCompIso (g)^*⟦ℚ̄_ℓ⟧ (f)^*⟦ℚ̄_ℓ⟧

end DerivedUpperStar

/-! ### The derived adjunction `Lf^* ⊣ Rf_*` -/

section Adjunction

/-- The derived adjunction `Lf^* ⊣ Rf_*` between the total derived functors of the pullback
and the pushforward on module objects over `ℚ̄_ℓ`, induced by the adjunction `f^* ⊣ f_*` of
`ProEtale.PadicAlgClRing.upperStarLowerStarAdjunction`: the left adjoint is derived via the
K-flat left derivability structure on `D(Mod_{ℚ̄_ℓ,Y})` and the right adjoint via the
K-injective right derivability structure on `D(Mod_{ℚ̄_ℓ,X})`. -/
noncomputable def derivedUpperStarLowerStarAdjunction : L((f)^*⟦ℚ̄_ℓ⟧) ⊣ R((f)_*⟦ℚ̄_ℓ⟧) :=
  (upperStarLowerStarAdjunction ℓ f).derivedAdjunction

instance : L((f)^*⟦ℚ̄_ℓ⟧).IsLeftAdjoint := (derivedUpperStarLowerStarAdjunction ℓ f).isLeftAdjoint

instance : R((f)_*⟦ℚ̄_ℓ⟧).IsRightAdjoint := (derivedUpperStarLowerStarAdjunction ℓ f).isRightAdjoint

/-- The bounded below version of `ProEtale.PadicAlgClRing.derivedUpperStarLowerStarAdjunction`:
since the pullback `f^*` on module objects is exact, its derived functor on the bounded below
derived categories is the levelwise functor `D+((f)^*⟦ℚ̄_ℓ⟧)`, and it is left adjoint to the
right derived functor `R+((f)_*⟦ℚ̄_ℓ⟧)` of the pushforward on the bounded below derived
categories. -/
noncomputable def derivedUpperStarLowerStarAdjunctionPlus :
    D+((f)^*⟦ℚ̄_ℓ⟧) ⊣ R+((f)_*⟦ℚ̄_ℓ⟧) :=
  (upperStarLowerStarAdjunction ℓ f).derivedAdjunctionPlus

end Adjunction

end AlgebraicGeometry.ProEtale.PadicAlgClRing
