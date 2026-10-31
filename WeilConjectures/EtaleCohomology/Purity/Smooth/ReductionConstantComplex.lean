/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ReductionKummerClass
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit

/-!
# The transpose of the counit `Ψ Λ ≅ Λ'` of the derived extension of scalars

Let `Ψ` be the derived extension of scalars along a surjection `ρ : Λ →+* Λ'` with principal
kernel, left adjoint to the restriction of scalars `Res`. The transpose under `Ψ ⊣ Res` of the
counit `η : Ψ Λ_X ≅ Λ'_X` of the oplax monoidal `Ψ` is the image of the canonical map
`Λ ⟶ Res Λ'` of the homotopy categories
(`AlgebraicGeometry.Etale.homotopyUnitRestrictScalars`), the unit of the extension and
restriction of scalars followed by `Res η`
(`AlgebraicGeometry.Etale.unit_app_comp_map_derivedExtendScalarsConstantComplexEtaIso_hom`).
On the image of the homotopy category, the commutation `Lt^* Res ≅ Res Lt^*` is induced by
`t^* Res ≅ Res t^*`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarRestrictScalarsIso_hom_app_Qh_obj`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

/-- The counit `Ψ Λ_X ⟶ Λ'_X` of the oplax monoidal derived extension of scalars, in terms of the
counit of the left derived functor. -/
lemma derivedExtendScalarsConstantComplexEtaIso_hom_eq (X : Scheme.{u}) :
    haveI := DerivedCategory.isIso_ε_Qh (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    (derivedExtendScalarsConstantComplexEtaIso hρ ha X).hom =
      (derivedExtendScalars hρ ha X).map (ε DerivedCategory.Qh) ≫
        (derivedExtendScalarsCounit hρ ha X).app (𝟙_ _) ≫
        DerivedCategory.Qh.map
          (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))) ≫
        inv (ε DerivedCategory.Qh) :=
  rfl

variable (ρ) in
/-- The canonical map `Λ ⟶ Res Λ'` in the homotopy category: the unit of the extension and
restriction of scalars at the unit, followed by the restriction of scalars of the counit `η` of
the oplax monoidal extension of scalars. -/
noncomputable def homotopyUnitRestrictScalars (X : Scheme.{u}) :
    𝟙_ (HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) ⟶
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj (𝟙_ _) :=
  ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).unit.app
      (𝟙_ _) ≫
    ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).map
      (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)))

/-- **The transpose of `Ψ Λ_X ≅ Λ'_X`** under `Ψ ⊣ Res` is the canonical map `Λ_X ⟶ Res Λ'_X`
of the homotopy category (`homotopyUnitRestrictScalars`). -/
lemma unit_app_comp_map_derivedExtendScalarsConstantComplexEtaIso_hom (X : Scheme.{u}) :
    haveI := DerivedCategory.isIso_ε_Qh (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
    (derivedExtendScalarsAdjunction hρ ha X).unit.app (constantComplex Λ X) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (derivedExtendScalarsConstantComplexEtaIso hρ ha X).hom =
      ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map (homotopyUnitRestrictScalars ρ X) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.inv.app
          (𝟙_ _) ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (inv (ε DerivedCategory.Qh)) := by
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  have hU := (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ
    ).derivedAdjunctionMapDerivedCategory_unit_app_fac (𝟙_ _)
  have hU' : (derivedExtendScalarsAdjunction hρ ha X).unit.app (DerivedCategory.Qh.obj (𝟙_ _)) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
        ((derivedExtendScalarsCounit hρ ha X).app (𝟙_ _)) =
      DerivedCategory.Qh.map (((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ
        ).mapHomotopyCategory (.up ℤ)).unit.app (𝟙_ _)) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.inv.app _ := by
    rw [← hU]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    erw [Category.comp_id]
    rfl
  have hn : DerivedCategory.Qh.map (((Sheaf.restrictScalars X.smallEtaleTopology ρ
      ).mapHomotopyCategory (.up ℤ)).map
        (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)))) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.inv.app _ =
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.inv.app _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (DerivedCategory.Qh.map
          (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)))) :=
    ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.inv.naturality
      (η ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))) :)
  rw [derivedExtendScalarsConstantComplexEtaIso_hom_eq]
  simp only [Functor.map_comp]
  erw [(derivedExtendScalarsAdjunction hρ ha X).unit_naturality_assoc]
  rw [reassoc_of% hU',
    ← reassoc_of% hn, homotopyUnitRestrictScalars, Functor.map_comp, Category.assoc]

section Pullback

variable {X S : Scheme.{u}} (t : X ⟶ S)

variable (Λ) in
/-- The identification `Lt^* Λ_S ≅ Λ_X` in terms of the counit of the left derived functor. -/
lemma leftDerivedUpperStarConstantComplexIso_hom_eq_counit :
    haveI := DerivedCategory.isIso_ε_Qh (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (leftDerivedUpperStarConstantComplexIso Λ t).hom =
      (L((t)^*[ModuleCat.{u + 1} Λ])).map (ε DerivedCategory.Qh) ≫
        (t)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctorCounit.app (𝟙_ _) ≫
        DerivedCategory.Qh.map (η ((t)^*[ModuleCat.{u + 1} Λ].mapHomotopyCategory (.up ℤ))) ≫
        inv (ε DerivedCategory.Qh) :=
  rfl

variable (ρ) in
/-- The commutation `t^* Res ≅ Res t^*` of the pullback with the restriction of scalars, on the
homotopy categories. -/
noncomputable def mapHomotopyCategoryUpperStarRestrictScalars
    (K : HomotopyCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ)) :
    ((t)^*[ModuleCat.{u + 1} Λ].mapHomotopyCategory (.up ℤ)).obj
        (((Sheaf.restrictScalars S.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj K) ⟶
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj
        (((t)^*[ModuleCat.{u + 1} Λ'].mapHomotopyCategory (.up ℤ)).obj K) :=
  (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
    (NatTrans.mapHomotopyCategory (upperStarRestrictScalarsIso ρ t).hom (.up ℤ)).app K ≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K

variable (ρ) in
/-- On the image of an object of the homotopy category, the commutation `Lt^* Res ≅ Res Lt^*` is
induced, through the counits of the derived pullbacks, by `t^* Res ≅ Res t^*`. -/
lemma leftDerivedUpperStarRestrictScalarsIso_hom_app_Qh_obj
    (K : HomotopyCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ)) :
    (leftDerivedUpperStarRestrictScalarsIso ρ t).hom.app (DerivedCategory.Qh.obj K) ≫
      (Sheaf.derivedRestrictScalars _ ρ).map
        ((t)^*[ModuleCat.{u + 1} Λ'].leftDerivedFunctorCounit.app K) ≫
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app
        (((t)^*[ModuleCat.{u + 1} Λ'].mapHomotopyCategory (.up ℤ)).obj K) =
    L((t)^*[ModuleCat.{u + 1} Λ]).map
        ((Sheaf.restrictScalars S.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app K) ≫
      (t)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctorCounit.app
        (((Sheaf.restrictScalars _ ρ).mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map (mapHomotopyCategoryUpperStarRestrictScalars ρ t K) :=
  Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj_comp_counit
    (R₁ := Sheaf.restrictScalars S.smallEtaleTopology ρ)
    (R₂ := Sheaf.restrictScalars X.smallEtaleTopology ρ) _ _
    (t)^*[ModuleCat.{u + 1} Λ].leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac _ _
    (t)^*[ModuleCat.{u + 1} Λ'].leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac
    (upperStarRestrictScalarsIso ρ t) _ rfl K

end Pullback

end Etale

end AlgebraicGeometry
