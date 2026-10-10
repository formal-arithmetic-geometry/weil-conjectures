/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Colimit.SubfieldSixFunctors
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Derived.OpenImmersionLowerShriek

/-!

# Compatibility of the six functors with the extension of `ℓ`-adic coefficients

Let `ℓ` be a prime, `E ≤ F` finite subextensions of `ℚ_ℓ` inside `ℚ̄_ℓ`
(`PadicAlgCl.FiniteSubext ℓ`) and `Ω = ℚ̄_ℓ`. For a scheme `X`, the coefficient inclusions
`ι : E_X ⟶ F_X` (`ProEtale.padicSubfieldRingObjMap`) and `ι : E_X ⟶ ℚ̄_ℓ,X`
(`ProEtale.padicSubfieldSheafToPadicAlgClSheaf`) induce the *derived extensions of scalars*
```
T^X_{E,F} = F_X ⊗ᴸ_{E_X} - = L(Ext_ι) : D(Mod_{E_X}) ⥤ D(Mod_{F_X}),
T^X_{E,Ω} = ℚ̄_ℓ,X ⊗ᴸ_{E_X} - = L(Ext_ι) : D(Mod_{E_X}) ⥤ D(Mod_{ℚ̄_ℓ,X}),
```
and this file constructs the *canonical comparison transformations* between these and the
derived functors `Lf^*`, `Rf_*`, `Rf_!` on module objects, for a morphism of schemes
`f : X ⟶ Y`: over `E_X` these are the functors `(f)^*⟦ℓ, E⟧`, `(f)_*⟦ℓ, E⟧`, `R(f)_!⟦ℓ, E⟧` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Colimit.SubfieldSixFunctors`,
over `ℚ̄_ℓ,X` the functors `(f)^*⟦ℚ̄_ℓ⟧`, `(f)_*⟦ℚ̄_ℓ⟧`, `R(f)_!⟦ℚ̄_ℓ⟧` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl`.

All comparisons are built from the commutative squares **(A0.3)** of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.Colimit.CoefficientHom`,
```
      E_Y ---ι---> F_Y                  E_Y ---ι---> ℚ̄_ℓ,Y
       |            |                    |             |
      η_f          η_f                  η_f           η_f
       ↓            ↓                    ↓             ↓
    f_* E_X -f_* ι-> f_* F_X          f_* E_X -f_* ι-> f_* ℚ̄_ℓ,X
```
by the mate and conjugate constructions of
`WeilConjectures.CategoryTheory.ModuleObjects.ChangeOfScalarsSquare`, in the same way for the
two coefficient changes:

* **restriction of scalars commutes with the pushforward**, strictly
  (`ProEtale.padicSubfieldComapLowerStarIso`, `ProEtale.padicAlgClComapLowerStarIso`): both
  composites are `mapMod(f_*)` followed by the restriction of scalars along the common composite
  of the square; and in the derived categories (`ProEtale.padicSubfieldDerivedComapLowerStarIso`,
  `ProEtale.padicAlgClDerivedComapLowerStarIso`), using that the restriction of scalars along a
  flat inclusion preserves K-injective complexes;
* **(Pull)** `Lf^*_E ⋙ T^X ≅ T^Y ⋙ Lf^*_F` and `Lf^*_E ⋙ T^X ≅ T^Y ⋙ Lf^*_Ω`
  (`ProEtale.padicSubfieldDerivedPullIso`, `ProEtale.padicAlgClDerivedPullIso`, and the underived
  `ProEtale.padicSubfieldPullIso`, `ProEtale.padicAlgClPullIso`): the *conjugates* of the previous
  isomorphisms along `Lf^* ⊣ Rf_*` and `L(Ext) ⊣ D(Res)`, hence isomorphisms on all unbounded
  objects;
* **(Push)** `Rf_*^E ⋙ T^Y ⟶ T^X ⋙ Rf_*^F` and `Rf_*^E ⋙ T^Y ⟶ T^X ⋙ Rf_*^Ω`
  (`ProEtale.padicSubfieldDerivedPushHom`, `ProEtale.padicAlgClDerivedPushHom`, and the underived
  `ProEtale.padicSubfieldPushHom`, `ProEtale.padicAlgClPushHom`): the *mates* of the previous
  isomorphisms. For a finite extension `F/E` they are isomorphisms on all unbounded objects
  (`ProEtale.isIso_padicSubfieldDerivedPushHom`); for `E ⊆ Ω` they are isomorphisms on all
  unbounded objects when `f` is proper (`ProEtale.isIso_padicAlgClDerivedPushHom_of_isProper`),
  but not for an arbitrary `f`;
* for an open immersion `j`, **restriction of scalars commutes with `j_!` and `j^*`**, and the
  comparison `j_!^E ⋙ T^X ≅ T^U ⋙ j_!^F` is an *isomorphism*, being the conjugate of the latter
  along `j_! ⊣ j^*` (`ProEtale.padicSubfieldOpenImmersionShriekIso`,
  `ProEtale.padicAlgClOpenImmersionShriekIso`, and their derived versions);
* **(Shriek)** `Rf_!^E ⋙ T^Y ⟶ T^X ⋙ Rf_!^F` and `Rf_!^E ⋙ T^Y ⟶ T^X ⋙ Rf_!^Ω`
  (`ProEtale.padicSubfieldDerivedLowerShriekHom`, `ProEtale.padicAlgClDerivedLowerShriekHom`),
  for `Rf_! = Di_! ⋙ Rg_*` attached to the chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`:
  the derived (Push) for the proper `g` followed by the derived (Shriek) isomorphism for the open
  immersion `i`. Since `g` is proper, both are isomorphisms on all unbounded objects
  (`ProEtale.isIso_padicSubfieldDerivedLowerShriekHom`,
  `ProEtale.isIso_padicAlgClDerivedLowerShriekHom`).

The six functors themselves are unchanged and remain defined on the unbounded derived
categories.

## Sorried input

* **(A0.2)** `ProEtale.preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap`: for finite
  subextensions `E ≤ F`, the extension of scalars `F_X ⊗_{E_X} -` is exact, i.e. `F_X` is flat
  over `E_X`. Indeed `F_X` is finite free over `E_X`: an `E`-basis `b₁, …, bₙ` of `F` gives
  `C(-, F) ≅ C(-, E)^n`, `h ↦ (hᵢ)` with `h = ∑ hᵢ bᵢ`.
* **(A0.2)** `ProEtale.preservesFiniteLimits_extendScalars_padicSubfieldSheafToPadicAlgClSheaf`:
  for a finite subextension `E`, the extension of scalars `ℚ̄_ℓ,X ⊗_{E_X} -` is exact, i.e.
  `ℚ̄_ℓ,X` is flat over `E_X`: it is the sheafification of the filtered union of the `F_X`,
  `F ≥ E` (`ProEtale.padicAlgClSheaf_isColimit`), each of which is finite free over `E_X`.
* `ProEtale.isIso_padicSubfieldDerivedPushHom`: for a finite extension `F/E`, (Push) is an
  isomorphism on all unbounded objects, since `F_X ≅ E_X^n` reduces it to the compatibility of
  `Rf_*` with finite direct sums.
* `ProEtale.isIso_padicAlgClDerivedPushHom_of_isProper`: for `E ⊆ Ω` and `f` proper, (Push) is
  an isomorphism on all unbounded objects: `Rf_*` has a right adjoint `Rf^!`
  (`ProEtale.PadicAlgClRing.isLeftAdjoint_rightDerivedLowerStar_of_isProper`), hence commutes
  with the coproducts through which `ℚ̄_ℓ,X ⊗ᴸ_{E_X} -` is computed from the finite stages. For a
  general `f` this fails, and (Push) is an isomorphism only at objects at which `Rf_*` commutes
  with the relevant coproducts; no such statement is made here.

The compatibilities with the derived tensor product, the derived hom and `Rf^!` are not treated:
they require the strong monoidality of the extension of scalars, respectively perfectness or
duality hypotheses, which are not formalized.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonObj Abelian

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl PadicSubfieldRing PadicAlgClRing

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-! ### Flatness of the coefficient inclusions -/

section Flat

variable (X : Scheme.{u})

/-- **(A0.2)** For finite subextensions `E ≤ F`, the extension of scalars along `E_X ⟶ F_X` is
exact: `F_X` is finite free, in particular flat, over `E_X`. See the module docstring. -/
instance preservesFiniteLimits_extendScalars_padicSubfieldRingObjMap {E F : FiniteSubext ℓ}
    (h : E ≤ F) : PreservesFiniteLimits (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) :=
  sorry

/-- **(A0.2)** For a finite subextension `E`, the extension of scalars along `E_X ⟶ ℚ̄_ℓ,X` is
exact: `ℚ̄_ℓ,X` is flat over `E_X`, being a filtered colimit of finite free `E_X`-modules. See
the module docstring. -/
instance preservesFiniteLimits_extendScalars_padicSubfieldSheafToPadicAlgClSheaf
    (E : FiniteSubext ℓ) :
    PreservesFiniteLimits (Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)) :=
  sorry

instance preservesHomology_extendScalars_padicSubfieldRingObjMap {E F : FiniteSubext ℓ}
    (h : E ≤ F) : (Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)).PreservesHomology := {}

instance preservesHomology_extendScalars_padicSubfieldSheafToPadicAlgClSheaf
    (E : FiniteSubext ℓ) :
    (Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)).PreservesHomology := {}

/-- The restriction of scalars along the flat inclusion `E_X ⟶ F_X` preserves K-injective
complexes, its left adjoint being exact. -/
instance preservesKInjectiveComplexes_comap_padicSubfieldRingObjMap {E F : FiniteSubext ℓ}
    (h : E ≤ F) :
    (Mod.comap (padicSubfieldRingObjMap X ℓ h) :
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F) ⥤
        Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)
      ).PreservesKInjectiveComplexes :=
  (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ h)).preservesKInjectiveComplexes

/-- The restriction of scalars along the flat inclusion `E_X ⟶ ℚ̄_ℓ,X` preserves K-injective
complexes, its left adjoint being exact. -/
instance preservesKInjectiveComplexes_comap_padicSubfieldSheafToPadicAlgClSheaf
    (E : FiniteSubext ℓ) :
    (Mod.comap (padicSubfieldSheafToPadicAlgClSheaf X ℓ E) :
      Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClSheaf X ℓ) ⥤
        Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)
      ).PreservesKInjectiveComplexes :=
  (Mod.extendRestrictAdjunction
    (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)).preservesKInjectiveComplexes

end Flat

/-! ### Finite extensions `F/E`: pushforward and pullback -/

section FiniteExtension

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {E F : FiniteSubext ℓ} (h : E ≤ F)

/-- Restriction of scalars commutes with the pushforward:
`f_*^F ⋙ Res_ι ≅ Res_ι ⋙ f_*^E`, both being `mapMod(f_*)` followed by the restriction of scalars
along the common composite of the square `ι ≫ η_f = η_f ≫ f_* ι`. -/
noncomputable def padicSubfieldComapLowerStarIso :
    (f)_*⟦ℓ, F⟧ ⋙ Mod.comap (padicSubfieldRingObjMap Y ℓ h) ≅
      Mod.comap (padicSubfieldRingObjMap X ℓ h) ⋙ (f)_*⟦ℓ, E⟧ :=
  Mod.comapMapModComapIso (f)_*[Ab.{u + 1}] (padicSubfieldRingObjMap X ℓ h)
    (padicSubfieldRingObjMap Y ℓ h) (padicSubfieldPushforwardHom ℓ f E)
    (padicSubfieldPushforwardHom ℓ f F) (padicSubfieldPushforwardHom_comp_map ℓ f h).symm

/-- The mates `α_f : f^* E_Y ⟶ E_X` and `α_f : f^* F_Y ⟶ F_X` form a commutative square with the
inclusions: `f^* ι ≫ α_f = α_f ≫ ι`. -/
lemma padicSubfieldPullbackHom_square :
    (f)^*[Ab.{u + 1}].map (padicSubfieldRingObjMap Y ℓ h) ≫ padicSubfieldPullbackHom ℓ f F =
      padicSubfieldPullbackHom ℓ f E ≫ padicSubfieldRingObjMap X ℓ h :=
  Adjunction.pullbackHom_square (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
    (padicSubfieldRingObjMap X ℓ h) (padicSubfieldRingObjMap Y ℓ h)
    (padicSubfieldPushforwardHom ℓ f E) (padicSubfieldPushforwardHom ℓ f F)
    (padicSubfieldPushforwardHom_comp_map ℓ f h).symm

/-- **(Pull)**, underived: `f^*_E ⋙ Ext_ι ≅ Ext_ι ⋙ f^*_F`, the conjugate of
`padicSubfieldComapLowerStarIso` along `f^* ⊣ f_*` and `Ext ⊣ Res`. -/
noncomputable def padicSubfieldPullIso :
    (f)^*⟦ℓ, E⟧ ⋙ Mod.extendScalars (padicSubfieldRingObjMap X ℓ h) ≅
      Mod.extendScalars (padicSubfieldRingObjMap Y ℓ h) ⋙ (f)^*⟦ℓ, F⟧ :=
  Adjunction.pullIsoOfComapIso (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ h))
    (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap Y ℓ h))
    (PadicSubfieldRing.upperStarLowerStarAdjunction ℓ f E)
    (PadicSubfieldRing.upperStarLowerStarAdjunction ℓ f F)
    (padicSubfieldComapLowerStarIso ℓ f h)

/-- **(Push)**, underived: the canonical comparison `f_*^E ⋙ Ext_ι ⟶ Ext_ι ⋙ f_*^F`, the mate of
`padicSubfieldComapLowerStarIso` along `Ext ⊣ Res`. -/
noncomputable def padicSubfieldPushHom :
    (f)_*⟦ℓ, E⟧ ⋙ Mod.extendScalars (padicSubfieldRingObjMap Y ℓ h) ⟶
      Mod.extendScalars (padicSubfieldRingObjMap X ℓ h) ⋙ (f)_*⟦ℓ, F⟧ :=
  Adjunction.pushHomOfComapIso (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ h))
    (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap Y ℓ h))
    (padicSubfieldComapLowerStarIso ℓ f h)

/-- Restriction of scalars commutes with the derived pushforward:
`Rf_*^F ⋙ D(Res_ι) ≅ D(Res_ι) ⋙ Rf_*^E`. The restriction of scalars is exact and, `F_X` being flat
over `E_X`, preserves K-injective complexes, so both sides are the right derived functor of the
two equal composites of `padicSubfieldComapLowerStarIso`. -/
noncomputable def padicSubfieldDerivedComapLowerStarIso :
    R((f)_*⟦ℓ, F⟧) ⋙ D(Mod.comap (padicSubfieldRingObjMap Y ℓ h)) ≅
      D(Mod.comap (padicSubfieldRingObjMap X ℓ h)) ⋙ R((f)_*⟦ℓ, E⟧) :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (f)_*⟦ℓ, F⟧
      (Mod.comap (padicSubfieldRingObjMap Y ℓ h))).symm ≪≫
    Functor.rightDerivedFunctorNatIso (padicSubfieldComapLowerStarIso ℓ f h) ≪≫
    Functor.rightDerivedFunctorCompIso (Mod.comap (padicSubfieldRingObjMap X ℓ h)) (f)_*⟦ℓ, E⟧ ≪≫
    Functor.isoWhiskerRight
      (Mod.comap (padicSubfieldRingObjMap X ℓ h)).rightDerivedFunctorIsoMapDerivedCategory
      R((f)_*⟦ℓ, E⟧)

/-- **(Pull)** for a finite extension `F/E`: `Lf^*_E ⋙ T^X_{E,F} ≅ T^Y_{E,F} ⋙ Lf^*_F`, the
conjugate of `padicSubfieldDerivedComapLowerStarIso` along the derived adjunctions. It is an
isomorphism on all unbounded objects. -/
noncomputable def padicSubfieldDerivedPullIso :
    L((f)^*⟦ℓ, E⟧) ⋙ L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) ≅
      L(Mod.extendScalars (padicSubfieldRingObjMap Y ℓ h)) ⋙ L((f)^*⟦ℓ, F⟧) :=
  Adjunction.pullIsoOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap X ℓ h))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap Y ℓ h))
    (PadicSubfieldRing.derivedUpperStarLowerStarAdjunction ℓ f E)
    (PadicSubfieldRing.derivedUpperStarLowerStarAdjunction ℓ f F)
    (padicSubfieldDerivedComapLowerStarIso ℓ f h)

/-- **(Push)** for a finite extension `F/E`: the canonical comparison
`Rf_*^E ⋙ T^Y_{E,F} ⟶ T^X_{E,F} ⋙ Rf_*^F`, the mate of `padicSubfieldDerivedComapLowerStarIso`
along `L(Ext) ⊣ D(Res)`. -/
noncomputable def padicSubfieldDerivedPushHom :
    R((f)_*⟦ℓ, E⟧) ⋙ L(Mod.extendScalars (padicSubfieldRingObjMap Y ℓ h)) ⟶
      L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) ⋙ R((f)_*⟦ℓ, F⟧) :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap X ℓ h))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap Y ℓ h))
    (padicSubfieldDerivedComapLowerStarIso ℓ f h)

/-- **(Push)** is an isomorphism for a finite extension `F/E`, on all unbounded objects: `F_X`
is finite free over `E_X`, so both sides are finite direct sums of copies of `Rf_*^E`. See the
module docstring. -/
instance isIso_padicSubfieldDerivedPushHom : IsIso (padicSubfieldDerivedPushHom ℓ f h) :=
  sorry

end FiniteExtension

/-! ### Finite extensions `F/E`: extension by zero along an open immersion -/

section FiniteExtensionOpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] {E F : FiniteSubext ℓ} (h : E ≤ F)

/-- Restriction of scalars commutes with the extension by zero along an open immersion:
`j_!^F ⋙ Res_ι ≅ Res_ι ⋙ j_!^E`, by the naturality of the projection formula and the square of
the mates `α_j`. -/
noncomputable def padicSubfieldComapOpenImmersionLowerShriekIso :
    (j)_!open⟦ℓ, F⟧ ⋙ Mod.comap (padicSubfieldRingObjMap X ℓ h) ≅
      Mod.comap (padicSubfieldRingObjMap U ℓ h) ⋙ (j)_!open⟦ℓ, E⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Mod.comap (padicSubfieldPullbackHom ℓ j F))
      ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1}
        j).projectionFormula.mapModLeftComapIso (padicSubfieldRingObjMap X ℓ h)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Mod.comapComp _ _).symm ≪≫
      Mod.comapIsoOfEq (padicSubfieldPullbackHom_square ℓ j h) ≪≫ Mod.comapComp _ _) _ ≪≫
    Functor.associator _ _ _

/-- For an open immersion `j`, restriction of scalars commutes with the pullback:
`j^*_F ⋙ Res_ι ≅ Res_ι ⋙ j^*_E`, since the mates `α_j` are isomorphisms. -/
noncomputable def padicSubfieldComapUpperStarIso_of_isOpenImmersion :
    (j)^*⟦ℓ, F⟧ ⋙ Mod.comap (padicSubfieldRingObjMap U ℓ h) ≅
      Mod.comap (padicSubfieldRingObjMap X ℓ h) ⋙ (j)^*⟦ℓ, E⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((j)^*[Ab.{u + 1}].mapMod (R := padicSubfieldRingObj X ℓ F))
      (Mod.extendScalarsComapIsoOfIsIso ((j)^*[Ab.{u + 1}].map (padicSubfieldRingObjMap X ℓ h))
        (padicSubfieldRingObjMap U ℓ h) (padicSubfieldPullbackHom ℓ j E)
        (padicSubfieldPullbackHom ℓ j F) (padicSubfieldPullbackHom_square ℓ j h).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((j)^*[Ab.{u + 1}].mapModComapIso (padicSubfieldRingObjMap X ℓ h)).symm
      (Mod.extendScalars (padicSubfieldPullbackHom ℓ j E)) ≪≫
    Functor.associator _ _ _

/-- **(Shriek) for an open immersion**, underived: `j_!^E ⋙ Ext_ι ≅ Ext_ι ⋙ j_!^F`, the conjugate
of `padicSubfieldComapUpperStarIso_of_isOpenImmersion` along `j_! ⊣ j^*` and `Ext ⊣ Res`. -/
noncomputable def padicSubfieldOpenImmersionShriekIso :
    (j)_!open⟦ℓ, E⟧ ⋙ Mod.extendScalars (padicSubfieldRingObjMap X ℓ h) ≅
      Mod.extendScalars (padicSubfieldRingObjMap U ℓ h) ⋙ (j)_!open⟦ℓ, F⟧ :=
  (conjugateIsoEquiv ((Mod.extendRestrictAdjunction (padicSubfieldRingObjMap U ℓ h)).comp
    (PadicSubfieldRing.openImmersionLowerShriekUpperStarAdjunction ℓ j F))
    ((PadicSubfieldRing.openImmersionLowerShriekUpperStarAdjunction ℓ j E).comp
      (Mod.extendRestrictAdjunction (padicSubfieldRingObjMap X ℓ h)))).symm
    (padicSubfieldComapUpperStarIso_of_isOpenImmersion ℓ j h)

/-- Restriction of scalars commutes with the levelwise derived pullback along an open
immersion: `Dj^*_F ⋙ D(Res_ι) ≅ D(Res_ι) ⋙ Dj^*_E`. -/
noncomputable def padicSubfieldDerivedComapUpperStarIso_of_isOpenImmersion :
    D((j)^*⟦ℓ, F⟧) ⋙ D(Mod.comap (padicSubfieldRingObjMap U ℓ h)) ≅
      D(Mod.comap (padicSubfieldRingObjMap X ℓ h)) ⋙ D((j)^*⟦ℓ, E⟧) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (padicSubfieldComapUpperStarIso_of_isOpenImmersion ℓ j h) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- **(Shriek) for an open immersion**: `Dj_!^E ⋙ T^X_{E,F} ≅ T^U_{E,F} ⋙ Dj_!^F`, the conjugate of
`padicSubfieldDerivedComapUpperStarIso_of_isOpenImmersion` along the derived adjunctions
`Dj_! ⊣ Dj^*` and `L(Ext) ⊣ D(Res)`. It is an isomorphism on all unbounded objects. -/
noncomputable def padicSubfieldDerivedOpenImmersionShriekIso :
    D((j)_!open⟦ℓ, E⟧) ⋙ L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) ≅
      L(Mod.extendScalars (padicSubfieldRingObjMap U ℓ h)) ⋙ D((j)_!open⟦ℓ, F⟧) :=
  (conjugateIsoEquiv
    ((Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap U ℓ h)).comp
      (PadicSubfieldRing.derivedOpenImmersionLowerShriekUpperStarAdjunction ℓ j F))
    ((PadicSubfieldRing.derivedOpenImmersionLowerShriekUpperStarAdjunction ℓ j E).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap X ℓ h)))).symm
    (padicSubfieldDerivedComapUpperStarIso_of_isOpenImmersion ℓ j h)

end FiniteExtensionOpenImmersion

/-! ### Finite extensions `F/E`: lower shriek -/

section FiniteExtensionLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] {E F : FiniteSubext ℓ} (h : E ≤ F)

/-- **(Shriek)** for a finite extension `F/E`: the canonical comparison
`Rf_!^E ⋙ T^Y_{E,F} ⟶ T^X_{E,F} ⋙ Rf_!^F` for `Rf_! = Di_! ⋙ Rg_*` attached to the chosen
compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the derived (Push) comparison for the proper `g`
followed by the derived (Shriek) isomorphism for the open immersion `i`. -/
noncomputable def padicSubfieldDerivedLowerShriekHom :
    R(f)_!⟦ℓ, E⟧ ⋙ L(Mod.extendScalars (padicSubfieldRingObjMap Y ℓ h)) ⟶
      L(Mod.extendScalars (padicSubfieldRingObjMap X ℓ h)) ⋙ R(f)_!⟦ℓ, F⟧ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D(((HasCompactification.compactification f).i)_!open⟦ℓ, E⟧)
      (padicSubfieldDerivedPushHom ℓ (HasCompactification.compactification f).g h) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (padicSubfieldDerivedOpenImmersionShriekIso ℓ
        (HasCompactification.compactification f).i h).hom
      R(((HasCompactification.compactification f).g)_*⟦ℓ, F⟧) ≫
    (Functor.associator _ _ _).hom

/-- **(Shriek)** is an isomorphism for a finite extension `F/E`, on all unbounded objects: it is
assembled from (Push) for the proper part of the compactification, which is an isomorphism, and
the formal isomorphism for its open immersion. -/
instance isIso_padicSubfieldDerivedLowerShriekHom :
    IsIso (padicSubfieldDerivedLowerShriekHom ℓ f h) := by
  unfold padicSubfieldDerivedLowerShriekHom
  infer_instance

end FiniteExtensionLowerShriek

/-! ### The infinite extension `ℚ̄_ℓ/E`: pushforward and pullback -/

section PadicAlgCl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteSubext ℓ)

/-- Restriction of scalars commutes with the pushforward:
`f_*^Ω ⋙ Res_ι ≅ Res_ι ⋙ f_*^E`, both being `mapMod(f_*)` followed by the restriction of scalars
along the common composite of the square `ι ≫ η_f = η_f ≫ f_* ι`. -/
noncomputable def padicAlgClComapLowerStarIso :
    (f)_*⟦ℚ̄_ℓ⟧ ⋙ Mod.comap (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E) ≅
      Mod.comap (padicSubfieldSheafToPadicAlgClSheaf X ℓ E) ⋙ (f)_*⟦ℓ, E⟧ :=
  Mod.comapMapModComapIso (f)_*[Ab.{u + 1}] (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)
    (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E) (padicSubfieldPushforwardHom ℓ f E)
    (padicAlgClPushforwardHom ℓ f)
    (padicSubfieldPushforwardHom_comp_map_toPadicAlgClSheaf ℓ f E).symm

/-- The mates `α_f : f^* E_Y ⟶ E_X` and `α_f : f^* ℚ̄_ℓ,Y ⟶ ℚ̄_ℓ,X` form a commutative square with
the inclusions: `f^* ι ≫ α_f = α_f ≫ ι`. Neither `α_f` is assumed invertible. -/
lemma padicAlgClPullbackHom_square :
    (f)^*[Ab.{u + 1}].map (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E) ≫ padicAlgClPullbackHom ℓ f =
      padicSubfieldPullbackHom ℓ f E ≫ padicSubfieldSheafToPadicAlgClSheaf X ℓ E :=
  Adjunction.pullbackHom_square (ProEtale.upperStarLowerStarAdjunction Ab.{u + 1} f)
    (padicSubfieldSheafToPadicAlgClSheaf X ℓ E) (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E)
    (padicSubfieldPushforwardHom ℓ f E) (padicAlgClPushforwardHom ℓ f)
    (padicSubfieldPushforwardHom_comp_map_toPadicAlgClSheaf ℓ f E).symm

/-- **(Pull)**, underived: `f^*_E ⋙ Ext_ι ≅ Ext_ι ⋙ f^*_Ω`, the conjugate of
`padicAlgClComapLowerStarIso` along `f^* ⊣ f_*` and `Ext ⊣ Res`. -/
noncomputable def padicAlgClPullIso :
    (f)^*⟦ℓ, E⟧ ⋙ Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf X ℓ E) ≅
      Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E) ⋙ (f)^*⟦ℚ̄_ℓ⟧ :=
  Adjunction.pullIsoOfComapIso
    (Mod.extendRestrictAdjunction (padicSubfieldSheafToPadicAlgClSheaf X ℓ E))
    (Mod.extendRestrictAdjunction (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E))
    (PadicSubfieldRing.upperStarLowerStarAdjunction ℓ f E)
    (PadicAlgClRing.upperStarLowerStarAdjunction ℓ f)
    (padicAlgClComapLowerStarIso ℓ f E)

/-- **(Push)**, underived: the canonical comparison `f_*^E ⋙ Ext_ι ⟶ Ext_ι ⋙ f_*^Ω`, the mate of
`padicAlgClComapLowerStarIso` along `Ext ⊣ Res`. -/
noncomputable def padicAlgClPushHom :
    (f)_*⟦ℓ, E⟧ ⋙ Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E) ⟶
      Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf X ℓ E) ⋙ (f)_*⟦ℚ̄_ℓ⟧ :=
  Adjunction.pushHomOfComapIso
    (Mod.extendRestrictAdjunction (padicSubfieldSheafToPadicAlgClSheaf X ℓ E))
    (Mod.extendRestrictAdjunction (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E))
    (padicAlgClComapLowerStarIso ℓ f E)

/-- Restriction of scalars commutes with the derived pushforward:
`Rf_*^Ω ⋙ D(Res_ι) ≅ D(Res_ι) ⋙ Rf_*^E`, using that `ℚ̄_ℓ,X` is flat over `E_X`. -/
noncomputable def padicAlgClDerivedComapLowerStarIso :
    R((f)_*⟦ℚ̄_ℓ⟧) ⋙ D(Mod.comap (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E)) ≅
      D(Mod.comap (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)) ⋙ R((f)_*⟦ℓ, E⟧) :=
  (Functor.rightDerivedFunctorCompMapDerivedCategoryIso (f)_*⟦ℚ̄_ℓ⟧
      (Mod.comap (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E))).symm ≪≫
    Functor.rightDerivedFunctorNatIso (padicAlgClComapLowerStarIso ℓ f E) ≪≫
    Functor.rightDerivedFunctorCompIso (Mod.comap (padicSubfieldSheafToPadicAlgClSheaf X ℓ E))
      (f)_*⟦ℓ, E⟧ ≪≫
    Functor.isoWhiskerRight (Mod.comap
      (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)).rightDerivedFunctorIsoMapDerivedCategory
      R((f)_*⟦ℓ, E⟧)

/-- **(Pull)** for `E ⊆ ℚ̄_ℓ`: `Lf^*_E ⋙ T^X_{E,Ω} ≅ T^Y_{E,Ω} ⋙ Lf^*_Ω`, the conjugate of
`padicAlgClDerivedComapLowerStarIso` along the derived adjunctions. It is an isomorphism on all
unbounded objects. -/
noncomputable def padicAlgClDerivedPullIso :
    L((f)^*⟦ℓ, E⟧) ⋙ L(Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)) ≅
      L(Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E)) ⋙ L((f)^*⟦ℚ̄_ℓ⟧) :=
  Adjunction.pullIsoOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldSheafToPadicAlgClSheaf X ℓ E))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E))
    (PadicSubfieldRing.derivedUpperStarLowerStarAdjunction ℓ f E)
    (PadicAlgClRing.derivedUpperStarLowerStarAdjunction ℓ f)
    (padicAlgClDerivedComapLowerStarIso ℓ f E)

/-- **(Push)** for `E ⊆ ℚ̄_ℓ`: the canonical comparison `Rf_*^E ⋙ T^Y_{E,Ω} ⟶ T^X_{E,Ω} ⋙ Rf_*^Ω`,
the mate of `padicAlgClDerivedComapLowerStarIso` along `L(Ext) ⊣ D(Res)`. It is not an
isomorphism for an arbitrary `f`. -/
noncomputable def padicAlgClDerivedPushHom :
    R((f)_*⟦ℓ, E⟧) ⋙ L(Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E)) ⟶
      L(Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)) ⋙ R((f)_*⟦ℚ̄_ℓ⟧) :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldSheafToPadicAlgClSheaf X ℓ E))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E))
    (padicAlgClDerivedComapLowerStarIso ℓ f E)

/-- **(Push)** is an isomorphism for `E ⊆ ℚ̄_ℓ` and `f` *proper*, on all unbounded objects: `Rf_*`
then admits a right adjoint `Rf^!`, hence commutes with the coproducts through which the derived
extension of scalars along the flat `E_X ⟶ ℚ̄_ℓ,X` is computed. See the module docstring. -/
instance isIso_padicAlgClDerivedPushHom_of_isProper [IsProper f] :
    IsIso (padicAlgClDerivedPushHom ℓ f E) :=
  sorry

end PadicAlgCl

/-! ### The infinite extension `ℚ̄_ℓ/E`: extension by zero along an open immersion -/

section PadicAlgClOpenImmersion

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (E : FiniteSubext ℓ)

/-- Restriction of scalars commutes with the extension by zero along an open immersion:
`j_!^Ω ⋙ Res_ι ≅ Res_ι ⋙ j_!^E`. -/
noncomputable def padicAlgClComapOpenImmersionLowerShriekIso :
    (j)_!open⟦ℚ̄_ℓ⟧ ⋙ Mod.comap (padicSubfieldSheafToPadicAlgClSheaf X ℓ E) ≅
      Mod.comap (padicSubfieldSheafToPadicAlgClSheaf U ℓ E) ⋙ (j)_!open⟦ℓ, E⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Mod.comap (padicAlgClPullbackHom ℓ j))
      ((ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1}
        j).projectionFormula.mapModLeftComapIso (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight ((Mod.comapComp _ _).symm ≪≫
      Mod.comapIsoOfEq (padicAlgClPullbackHom_square ℓ j E) ≪≫ Mod.comapComp _ _) _ ≪≫
    Functor.associator _ _ _

/-- For an open immersion `j`, restriction of scalars commutes with the pullback:
`j^*_Ω ⋙ Res_ι ≅ Res_ι ⋙ j^*_E`, since the mates `α_j` are isomorphisms. -/
noncomputable def padicAlgClComapUpperStarIso_of_isOpenImmersion :
    (j)^*⟦ℚ̄_ℓ⟧ ⋙ Mod.comap (padicSubfieldSheafToPadicAlgClSheaf U ℓ E) ≅
      Mod.comap (padicSubfieldSheafToPadicAlgClSheaf X ℓ E) ⋙ (j)^*⟦ℓ, E⟧ :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft ((j)^*[Ab.{u + 1}].mapMod (R := padicAlgClSheaf X ℓ))
      (Mod.extendScalarsComapIsoOfIsIso
        ((j)^*[Ab.{u + 1}].map (padicSubfieldSheafToPadicAlgClSheaf X ℓ E))
        (padicSubfieldSheafToPadicAlgClSheaf U ℓ E) (padicSubfieldPullbackHom ℓ j E)
        (padicAlgClPullbackHom ℓ j) (padicAlgClPullbackHom_square ℓ j E).symm) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      ((j)^*[Ab.{u + 1}].mapModComapIso (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)).symm
      (Mod.extendScalars (padicSubfieldPullbackHom ℓ j E)) ≪≫
    Functor.associator _ _ _

/-- **(Shriek) for an open immersion**, underived: `j_!^E ⋙ Ext_ι ≅ Ext_ι ⋙ j_!^Ω`, the conjugate
of `padicAlgClComapUpperStarIso_of_isOpenImmersion` along `j_! ⊣ j^*` and `Ext ⊣ Res`. -/
noncomputable def padicAlgClOpenImmersionShriekIso :
    (j)_!open⟦ℓ, E⟧ ⋙ Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf X ℓ E) ≅
      Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf U ℓ E) ⋙ (j)_!open⟦ℚ̄_ℓ⟧ :=
  (conjugateIsoEquiv
    ((Mod.extendRestrictAdjunction (padicSubfieldSheafToPadicAlgClSheaf U ℓ E)).comp
      (PadicAlgClRing.openImmersionLowerShriekUpperStarAdjunction ℓ j))
    ((PadicSubfieldRing.openImmersionLowerShriekUpperStarAdjunction ℓ j E).comp
      (Mod.extendRestrictAdjunction (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)))).symm
    (padicAlgClComapUpperStarIso_of_isOpenImmersion ℓ j E)

/-- Restriction of scalars commutes with the levelwise derived pullback along an open
immersion: `Dj^*_Ω ⋙ D(Res_ι) ≅ D(Res_ι) ⋙ Dj^*_E`. -/
noncomputable def padicAlgClDerivedComapUpperStarIso_of_isOpenImmersion :
    D((j)^*⟦ℚ̄_ℓ⟧) ⋙ D(Mod.comap (padicSubfieldSheafToPadicAlgClSheaf U ℓ E)) ≅
      D(Mod.comap (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)) ⋙ D((j)^*⟦ℓ, E⟧) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (padicAlgClComapUpperStarIso_of_isOpenImmersion ℓ j E) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

/-- **(Shriek) for an open immersion**: `Dj_!^E ⋙ T^X_{E,Ω} ≅ T^U_{E,Ω} ⋙ Dj_!^Ω`, the conjugate of
`padicAlgClDerivedComapUpperStarIso_of_isOpenImmersion` along the derived adjunctions
`Dj_! ⊣ Dj^*` and `L(Ext) ⊣ D(Res)`. It is an isomorphism on all unbounded objects. -/
noncomputable def padicAlgClDerivedOpenImmersionShriekIso :
    D((j)_!open⟦ℓ, E⟧) ⋙ L(Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)) ≅
      L(Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf U ℓ E)) ⋙ D((j)_!open⟦ℚ̄_ℓ⟧) :=
  (conjugateIsoEquiv
    ((Mod.derivedExtendMapDerivedCategoryAdjunction
      (padicSubfieldSheafToPadicAlgClSheaf U ℓ E)).comp
      (PadicAlgClRing.derivedOpenImmersionLowerShriekUpperStarAdjunction ℓ j))
    ((PadicSubfieldRing.derivedOpenImmersionLowerShriekUpperStarAdjunction ℓ j E).comp
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)))).symm
    (padicAlgClDerivedComapUpperStarIso_of_isOpenImmersion ℓ j E)

end PadicAlgClOpenImmersion

/-! ### The infinite extension `ℚ̄_ℓ/E`: lower shriek -/

section PadicAlgClLowerShriek

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] (E : FiniteSubext ℓ)

/-- **(Shriek)** for `E ⊆ ℚ̄_ℓ`: the canonical comparison `Rf_!^E ⋙ T^Y_{E,Ω} ⟶ T^X_{E,Ω} ⋙ Rf_!^Ω`
for `Rf_! = Di_! ⋙ Rg_*` attached to the chosen compactification `X ⟶[i] Z ⟶[g] Y` of `f`: the
derived (Push) comparison for the proper `g` followed by the derived (Shriek) isomorphism for the
open immersion `i`. -/
noncomputable def padicAlgClDerivedLowerShriekHom :
    R(f)_!⟦ℓ, E⟧ ⋙ L(Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf Y ℓ E)) ⟶
      L(Mod.extendScalars (padicSubfieldSheafToPadicAlgClSheaf X ℓ E)) ⋙ R(f)_!⟦ℚ̄_ℓ⟧ :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft D(((HasCompactification.compactification f).i)_!open⟦ℓ, E⟧)
      (padicAlgClDerivedPushHom ℓ (HasCompactification.compactification f).g E) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (padicAlgClDerivedOpenImmersionShriekIso ℓ (HasCompactification.compactification f).i E).hom
      R(((HasCompactification.compactification f).g)_*⟦ℚ̄_ℓ⟧) ≫
    (Functor.associator _ _ _).hom

/-- **(Shriek)** is an isomorphism for `E ⊆ ℚ̄_ℓ`, on all unbounded objects: the proper part of
the compactification contributes (Push) for a proper morphism, which is an isomorphism, and its
open immersion contributes a formal isomorphism. -/
instance isIso_padicAlgClDerivedLowerShriekHom : IsIso (padicAlgClDerivedLowerShriekHom ℓ f E) := by
  unfold padicAlgClDerivedLowerShriekHom
  infer_instance

end PadicAlgClLowerShriek

end AlgebraicGeometry.ProEtale
