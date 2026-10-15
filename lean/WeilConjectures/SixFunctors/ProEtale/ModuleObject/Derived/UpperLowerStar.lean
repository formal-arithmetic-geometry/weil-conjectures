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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

/-!

# Derived upper star and lower star on module objects over `Λ`

Let `Λ` be a commutative condensed ring and `f : X ⟶ Y` a morphism of schemes. The derived
pullback and pushforward on the derived categories `D(Mod_{Λ_X})` of module objects over
`Λ_X = p_X^* Λ` are *not* given definitions of their own: as in
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar`, they are the
*total* derived functors, i.e. the generic derived-functor constructions of the folder
`WeilConjectures.CategoryTheory.DerivedCategory` applied to the underived functors `(f)^*⟦Λ⟧`
and `(f)_*⟦Λ⟧` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`:

| derived functor | notation | meaning |
| --- | --- | --- |
| `Rf_* : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_Y})` | `R((f)_*⟦Λ⟧)` | `(f)_*⟦Λ⟧.rightDerivedFunctor` |
| `Rf_* : D⁺(Mod_{Λ_X}) ⥤ D⁺(Mod_{Λ_Y})` | `R+((f)_*⟦Λ⟧)` | `rightDerivedFunctorPlus` |
| `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` | `L((f)^*⟦Λ⟧)` | `(f)^*⟦Λ⟧.leftDerivedFunctor` |
| `f^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` | `D((f)^*⟦Λ⟧)` | `(f)^*⟦Λ⟧.mapDerivedCategory` |
| `f^* : D⁺(Mod_{Λ_Y}) ⥤ D⁺(Mod_{Λ_X})` | `D+((f)^*⟦Λ⟧)` | `mapDerivedCategoryPlus` |

The derived pushforward is computed on K-injective resolutions in `Mod_{Λ_X}`, and the
derived pullback is the total left derived functor of `f^* = Λ_X ⊗_{f^* Λ_Y} f^*(-)`,
computed on K-flat resolutions in `Mod_{Λ_Y}`, that is
```
Lf^* M = Λ_X ⊗ᴸ_{f^* Λ_Y} f^* M,
```
the derived extension of scalars along `α_f` of the exact pullback `f^* M`; this is the
pullback of Bhatt–Scholze, Remark 6.8.15. The pullback `f^*` on module objects is exact, the
coefficient morphism `α_f` being an isomorphism
(`ProEtale.CondensedRing.preservesFiniteLimits_upperStar`, see
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`), so,
as for étale sheaves, `Lf^*` is canonically the levelwise functor `D((f)^*⟦Λ⟧)`
(`ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`), and on the bounded
below derived categories the pullback is the levelwise functor `D+((f)^*⟦Λ⟧)`, left adjoint to
`R+((f)_*⟦Λ⟧)` (`ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunctionPlus`).

The two displayed formulas are theorems about the total derived functors, not definitions:

* `ProEtale.CondensedRing.rightDerivedLowerStarIso`:
  `R((f)_*⟦Λ⟧) ≅ R(mapMod(f_*)) ⋙ D(Res_{η_f})`. The restriction of scalars along
  `η_f : Λ_Y ⟶ f_* Λ_X` is exact, so right deriving the composite
  `(f)_*⟦Λ⟧ = mapMod(f_*) ⋙ Res_{η_f}` amounts to right deriving `mapMod(f_*)` and restricting
  scalars levelwise (`Functor.rightDerivedFunctorCompMapDerivedCategoryIso`).
* `ProEtale.CondensedRing.leftDerivedUpperStarIso`:
  `L((f)^*⟦Λ⟧) ≅ D(mapMod(f^*)) ⋙ L(Ext_{α_f})`. The exact functor `mapMod(f^*)` preserves
  K-flat complexes, so left deriving the composite `(f)^*⟦Λ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` amounts
  to applying `mapMod(f^*)` levelwise and left deriving the extension of scalars, both being
  computed on the same K-flat resolution in `Mod_{Λ_Y}`
  (`Functor.leftDerivedFunctorCompMapDerivedCategoryIso`).

## Main results

- `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`: the derived adjunction
  `L((f)^*⟦Λ⟧) ⊣ R((f)_*⟦Λ⟧)`, induced by the adjunction `f^* ⊣ f_*` on module objects, and
  `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunctionPlus`: its bounded below
  version `D+((f)^*⟦Λ⟧) ⊣ R+((f)_*⟦Λ⟧)`.

- `ProEtale.CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory`: the derived pullback
  `L((f)^*⟦Λ⟧)` is the levelwise functor `D((f)^*⟦Λ⟧)`.

- `ProEtale.CondensedRing.leftDerivedUpperStarComp`: the composition isomorphism
  `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*`, obtained from the underived
  `ProEtale.CondensedRing.upperStarComp` through the levelwise functors.

- `ProEtale.CondensedRing.rightDerivedLowerStarIso` and
  `ProEtale.CondensedRing.leftDerivedUpperStarIso`: the computations of `Rf_*` and `Lf^*`
  described above.

## Sorried input

- `ProEtale.CondensedRing.preservesKFlatComplexes_mapMod_upperStar`: `mapMod(f^*)` sends
  K-flat complexes of `Λ_Y`-modules to K-flat complexes of `f^* Λ_Y`-modules. Indeed
  `f^*` is strong monoidal, exact and commutes with colimits, so it commutes with the relative
  tensor product of complexes of module objects and preserves acyclicity. From it follows that
  the pullback `(f)^*⟦Λ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` on module objects preserves
  quasi-isomorphisms between K-flat complexes
  (`ProEtale.CondensedRing.preservesKFlatQuasiIso_upperStar`), which is the functor-specific
  input of the K-flat machinery making `L((f)^*⟦Λ⟧)` meaningful; the other ingredient is that
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

-- Compatibility: additive upstream K-flat APIs, without replacing the live dependency.
universe wC wD wE vC vD vE uC uD uE

open CategoryTheory Limits

namespace CategoryTheory.Functor

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open MonoidalCategory

section PreservesKFlatComplexes

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [MonoidalCategory D] [MonoidalPreadditive D] [HasCountableCoproducts D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- An additive functor `F : C ⥤ D` between monoidal abelian categories *preserves K-flat
complexes* if it sends K-flat cochain complexes to K-flat cochain complexes. Together with
exactness, this is the hypothesis under which the left derived functor of a composite
`F ⋙ G` is `D(F) ⋙ LG`, see `Functor.leftDerivedFunctorCompMapDerivedCategoryIso`. -/
class PreservesKFlatComplexes (F : C ⥤ D) [F.Additive] : Prop where
  kFlat_map (K : CochainComplex C ℤ) (hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)

lemma kFlat_mapHomologicalComplex_obj (F : C ⥤ D) [F.Additive] [F.PreservesKFlatComplexes]
    (K : CochainComplex C ℤ) (hK : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K) :
    (HomologicalComplex.quasiIso D (.up ℤ)).kFlat
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
  PreservesKFlatComplexes.kFlat_map K hK

/-- If `F` is exact and preserves K-flat complexes and `G` preserves K-flat
quasi-isomorphisms, then so does `F ⋙ G`. -/
instance preservesKFlatQuasiIso_comp {E : Type uE} [Category.{vE} E] [Abelian E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [F.PreservesHomology]
    [F.PreservesKFlatComplexes] [G.PreservesKFlatQuasiIso] :
    (F ⋙ G).PreservesKFlatQuasiIso where
  quasiIso_map hK hL f _ :=
    G.quasiIso_mapHomologicalComplex_map_of_kFlat (F.kFlat_mapHomologicalComplex_obj _ hK)
      (F.kFlat_mapHomologicalComplex_obj _ hL) ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)

end PreservesKFlatComplexes

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]
  [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

section Composition

variable {E : Type uE} [Category.{vE} E] [Abelian E] [HasDerivedCategory.{wE} E]

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

section CompositionKFlat

variable (G : D ⥤ E) [G.Additive] [G.PreservesKFlatQuasiIso] [F.PreservesKFlatComplexes]

/-- The counit exhibiting `D(F) ⋙ LG` as a candidate left derived functor of
`(F ⋙ G).mapHomotopyCategory ⋙ Qh`, for an exact functor `F` preserving K-flat complexes: it
is assembled from the comparison `F.mapDerivedCategoryFactorsh`, the counit of `LG` and the
composition isomorphism of `mapHomotopyCategory`. -/
noncomputable def leftDerivedFunctorCompMapDerivedCategoryCounit :
    DerivedCategory.Qh ⋙ (F.mapDerivedCategory ⋙ G.leftDerivedFunctor) ⟶
      (F ⋙ G).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.mapDerivedCategoryFactorsh.hom G.leftDerivedFunctor ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ)) G.leftDerivedFunctorCounit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).hom
      DerivedCategory.Qh

/-- If `F` is exact and preserves K-flat complexes, then `D(F) ⋙ LG`, equipped with the counit
`leftDerivedFunctorCompMapDerivedCategoryCounit`, is a left derived functor of
`(F ⋙ G).mapHomotopyCategory ⋙ Qh`: by the K-flat left derivability structure it suffices that
the counit is an isomorphism on K-flat complexes, which holds since `D(F)` is computed
levelwise and the counit of `LG` is an isomorphism on the K-flat complex `F K`. -/
instance isLeftDerivedFunctor_mapDerivedCategory_comp_leftDerivedFunctor :
    (F.mapDerivedCategory ⋙ G.leftDerivedFunctor).IsLeftDerivedFunctor
      (leftDerivedFunctorCompMapDerivedCategoryCounit F G)
      (HomotopyCategory.quasiIso C (ComplexShape.up ℤ)) := by
  rw [(F ⋙ G).isLeftDerivedFunctor_iff_isIso_app_of_kFlat]
  intro K hK
  have h : IsIso (G.leftDerivedFunctorCounit.app
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K))) :=
    G.isIso_leftDerivedFunctorCounit_app_of_kFlat _ (F.kFlat_mapHomologicalComplex_obj K hK)
  dsimp [leftDerivedFunctorCompMapDerivedCategoryCounit]
  infer_instance

/-- **Composition with an exact functor preserving K-flat complexes**: for an exact functor
`F : C ⥤ D` preserving K-flat complexes and an additive functor `G : D ⥤ E` preserving K-flat
quasi-isomorphisms, `L(F ⋙ G) ≅ D(F) ⋙ LG`: the left derived functor of the composite is
computed by applying `F` levelwise and then `LG`. This is the left derived counterpart of
`Functor.rightDerivedFunctorCompMapDerivedCategoryIso`, the K-flat preservation hypothesis
replacing the (automatic) preservation of acyclicity by the exact functor. -/
noncomputable def leftDerivedFunctorCompMapDerivedCategoryIso :
    (F ⋙ G).leftDerivedFunctor ≅ F.mapDerivedCategory ⋙ G.leftDerivedFunctor :=
  leftDerivedUnique (F.mapDerivedCategory ⋙ G.leftDerivedFunctor) (F ⋙ G).leftDerivedFunctor
    (F ⋙ G).leftDerivedFunctorCounit (leftDerivedFunctorCompMapDerivedCategoryCounit F G)
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))

end CompositionKFlat

end Composition

end CategoryTheory.Functor


universe u

open scoped CategoryTheory.Obj

open CategoryTheory Abelian Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X Y : Scheme.{u}} (f : X ⟶ Y)

/-! ### The derived pushforward -/

section DerivedLowerStar

/-- The total right derived functor `Rf_* : D(Mod_{Λ_X}) ⥤ D(Mod_{Λ_Y})` of the
pushforward `f_*` on module objects over `Λ`, on the unbounded derived categories,
computed on K-injective resolutions.

It is not a definition of its own: it is the generic `Functor.rightDerivedFunctor`, written
`R(-)`, applied to the underived pushforward `(f)_*⟦Λ⟧`. -/
noncomputable example :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  R((f)_*⟦Λ⟧)

/-- The right derived functor `Rf_* : D⁺(Mod_{Λ_X}) ⥤ D⁺(Mod_{Λ_Y})` of the pushforward
`f_*` on module objects, on the *bounded below* derived categories: the generic
`Functor.rightDerivedFunctorPlus`, written `R+(-)`, applied to `(f)_*⟦Λ⟧`. -/
noncomputable example :
    DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)) ⥤
      DerivedCategory.Plus (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
        (condensedRingObj Λ Y)) :=
  R+((f)_*⟦Λ⟧)

/-- The derived pushforward on module objects is the total right derived functor of
`mapMod(f_*) : Mod_{Λ_X} ⥤ Mod_{f_* Λ_X}` followed by the levelwise restriction of scalars
along `η_f : Λ_Y ⟶ f_* Λ_X`: the restriction of scalars is exact, so right deriving the
composite `(f)_*⟦Λ⟧ = mapMod(f_*) ⋙ Res_{η_f}` amounts to right deriving `mapMod(f_*)` and
restricting scalars levelwise. -/
noncomputable def rightDerivedLowerStarIso :
    R((f)_*⟦Λ⟧) ≅
      R((f)_*[Ab.{u + 1}].mapMod (condensedRingObj Λ X)) ⋙
        D(Mod.comap (condensedPushforwardHom Λ f)) :=
  Functor.rightDerivedFunctorCompMapDerivedCategoryIso
    ((f)_*[Ab.{u + 1}].mapMod (condensedRingObj Λ X))
    (Mod.comap (condensedPushforwardHom Λ f))

end DerivedLowerStar

/-! ### The derived pullback -/

section DerivedUpperStar

instance preservesHomology_mapMod_upperStar :
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).PreservesHomology := {}

/-- The pullback `mapMod(f^*) : Mod_{Λ_Y} ⥤ Mod_{f^* Λ_Y}` sends K-flat complexes to
K-flat complexes. See the module docstring for the argument. -/
instance preservesKFlatComplexes_mapMod_upperStar :
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)).PreservesKFlatComplexes := sorry

/-- The pullback `(f)^*⟦Λ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` on module objects over `Λ` preserves
quasi-isomorphisms between K-flat complexes: `mapMod(f^*)` is exact and preserves K-flat
complexes, and the extension of scalars preserves quasi-isomorphisms between K-flat
complexes. This is the functor-specific input of the K-flat left derivability structure. -/
instance preservesKFlatQuasiIso_upperStar : (f)^*⟦Λ⟧.PreservesKFlatQuasiIso :=
  Functor.preservesKFlatQuasiIso_comp
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
    (Mod.extendScalars (condensedPullbackHom Λ f))

/-- The total left derived functor `Lf^* : D(Mod_{Λ_Y}) ⥤ D(Mod_{Λ_X})` of the pullback
`f^*` on module objects over `Λ`, on the unbounded derived categories, computed on K-flat
resolutions: `Lf^* M = Λ_X ⊗ᴸ_{f^* Λ_Y} f^* M`.

It is not a definition of its own: it is the generic `Functor.leftDerivedFunctor`, written
`L(-)`, applied to the underived pullback `(f)^*⟦Λ⟧`. -/
noncomputable example :
    DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj Λ Y)) ⥤
      DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
        (condensedRingObj Λ X)) :=
  L((f)^*⟦Λ⟧)

/-- The derived pullback on module objects is the levelwise pullback
`D(mapMod(f^*)) : D(Mod_{Λ_Y}) ⥤ D(Mod_{f^* Λ_Y})` followed by the derived extension of
scalars `Λ_X ⊗ᴸ_{f^* Λ_Y} -` along `α_f`: `mapMod(f^*)` is exact and preserves K-flat
complexes, so left deriving the composite `(f)^*⟦Λ⟧ = mapMod(f^*) ⋙ Ext_{α_f}` amounts to
applying `mapMod(f^*)` levelwise and left deriving the extension of scalars. -/
noncomputable def leftDerivedUpperStarIso :
    L((f)^*⟦Λ⟧) ≅
      D((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y)) ⋙
        L(Mod.extendScalars (condensedPullbackHom Λ f)) :=
  Functor.leftDerivedFunctorCompMapDerivedCategoryIso
    ((f)^*[Ab.{u + 1}].mapMod (condensedRingObj Λ Y))
    (Mod.extendScalars (condensedPullbackHom Λ f))

/-- The derived pullback on module objects is the levelwise functor: since `f^*` on module
objects is exact (`ProEtale.CondensedRing.preservesFiniteLimits_upperStar`), its total left
derived functor `L((f)^*⟦Λ⟧)`, computed via K-flat resolutions, is canonically isomorphic to the
functor `D((f)^*⟦Λ⟧)` induced by applying `f^*` levelwise. This is
`Functor.leftDerivedFunctorIsoMapDerivedCategory` at `f^*`. -/
noncomputable def leftDerivedUpperStarIsoMapDerivedCategory :
    L((f)^*⟦Λ⟧) ≅ D((f)^*⟦Λ⟧) :=
  (f)^*⟦Λ⟧.leftDerivedFunctorIsoMapDerivedCategory

/-- The composition isomorphism `L(f ≫ g)^* ≅ Lg^* ⋙ Lf^*` of derived pullbacks on module
objects over `Λ`, obtained from the underived composition isomorphism
`ProEtale.CondensedRing.upperStarComp` and the compatibility of left derivation with
`mapDerivedCategory` for exact functors. -/
noncomputable def leftDerivedUpperStarComp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    L((f ≫ g)^*⟦Λ⟧) ≅ L((g)^*⟦Λ⟧) ⋙ L((f)^*⟦Λ⟧) :=
  Functor.leftDerivedFunctorNatIso _ (upperStarComp Λ f g) ≪≫
    Functor.leftDerivedFunctorCompIso (g)^*⟦Λ⟧ (f)^*⟦Λ⟧

end DerivedUpperStar

/-! ### The derived adjunction `Lf^* ⊣ Rf_*` -/

section Adjunction

/-- The derived adjunction `Lf^* ⊣ Rf_*` between the total derived functors of the pullback
and the pushforward on module objects over `Λ`, induced by the adjunction `f^* ⊣ f_*` of
`ProEtale.CondensedRing.upperStarLowerStarAdjunction`: the left adjoint is derived via the
K-flat left derivability structure on `D(Mod_{Λ_Y})` and the right adjoint via the
K-injective right derivability structure on `D(Mod_{Λ_X})`. -/
noncomputable def derivedUpperStarLowerStarAdjunction : L((f)^*⟦Λ⟧) ⊣ R((f)_*⟦Λ⟧) :=
  (upperStarLowerStarAdjunction Λ f).derivedAdjunction

instance : L((f)^*⟦Λ⟧).IsLeftAdjoint := (derivedUpperStarLowerStarAdjunction Λ f).isLeftAdjoint

instance : R((f)_*⟦Λ⟧).IsRightAdjoint := (derivedUpperStarLowerStarAdjunction Λ f).isRightAdjoint

/-- The bounded below version of `ProEtale.CondensedRing.derivedUpperStarLowerStarAdjunction`:
since the pullback `f^*` on module objects is exact, its derived functor on the bounded below
derived categories is the levelwise functor `D+((f)^*⟦Λ⟧)`, and it is left adjoint to the right
derived functor `R+((f)_*⟦Λ⟧)` of the pushforward on the bounded below derived categories. -/
noncomputable def derivedUpperStarLowerStarAdjunctionPlus :
    D+((f)^*⟦Λ⟧) ⊣ R+((f)_*⟦Λ⟧) :=
  (upperStarLowerStarAdjunction Λ f).derivedAdjunctionPlus

end Adjunction

end AlgebraicGeometry.ProEtale.CondensedRing
