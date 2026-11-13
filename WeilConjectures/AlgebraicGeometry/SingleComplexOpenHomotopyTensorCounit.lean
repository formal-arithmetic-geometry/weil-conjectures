/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenDirectImageUnit
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenUnderivedTensorMate

/-! # Sectionwise counit identity for the open tensor comparison

## References

* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem map_homotopy_counit_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    (L : C ⥤ D) (R : D ⥤ C) (L₀ : E ⥤ F) (R₀ : F ⥤ E)
    (G : C ⥤ E) (H : D ⥤ F)
    [L.Additive] [R.Additive] [L₀.Additive] [R₀.Additive]
    [G.Additive] [H.Additive]
    (a : L ⊣ R) (a₀ : L₀ ⊣ R₀) (t : L ⋙ H ≅ G ⋙ L₀) (e : R ⋙ G ≅ H ⋙ R₀)
    (h : ∀ M, t.inv.app (R.obj M) ≫ H.map (a.counit.app M) =
      L₀.map (e.hom.app M) ≫ a₀.counit.app (H.obj M))
    (I : HomotopyCategory D (.up ℤ)) :
    let tH := Functor.mapHomotopyCategoryCompIso t (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm
    let eH := Functor.mapHomotopyCategoryCompIso e (.up ℤ) ≪≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm
    tH.inv.app ((R.mapHomotopyCategory (.up ℤ)).obj I) ≫
      (H.mapHomotopyCategory (.up ℤ)).map ((a.mapHomotopyCategory (.up ℤ)).counit.app I) =
    (L₀.mapHomotopyCategory (.up ℤ)).map (eH.hom.app I) ≫
      (a₀.mapHomotopyCategory (.up ℤ)).counit.app
        ((H.mapHomotopyCategory (.up ℤ)).obj I) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective I
  dsimp only
  erw [Adjunction.mapHomotopyCategory_counit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient F (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient F (.up ℤ)).map _ =
    (HomotopyCategory.quotient F (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient F (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply congrArg
  ext n
  change (𝟙 _ ≫ t.inv.app (R.obj (K.X n))) ≫ H.map (a.counit.app (K.X n)) =
    L₀.map (e.hom.app (K.X n) ≫ 𝟙 _) ≫ a₀.counit.app (H.obj (K.X n))
  simpa only [Category.id_comp, Category.comp_id] using h (K.X n)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Comparing the chosen adjunctions with the named homotopy comparisons needs this budget.
/-- The inverse tensor restriction comparison is the mate of the sectionwise
open direct-image comparison, evaluated on a homotopy complex. All arrows here
are in homotopy categories; there are no derived-category arrows or units. -/
theorem singleComplexOpen_homotopy_tensor_counit
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let b := Adjunction.mapHomotopyCategory (.up ℤ)
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    let b₀ := Adjunction.mapHomotopyCategory (.up ℤ)
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V)))
    (openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
        (morphismRestrict_ι f V)).inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
      (rX.mapHomotopyCategory (.up ℤ)).map (b.counit.app I) =
    ((Scheme.Modules.tensorPullback (f ∣_ V)).mapHomotopyCategory (.up ℤ)).map
        ((singleComplexOpenHomotopyDirectImageIso f V).hom.app I) ≫
      b₀.counit.app ((rX.mapHomotopyCategory (.up ℤ)).obj I) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let := schemeOpenRestriction_additive Y V
  let := schemeOpenRestriction_additive X (f ⁻¹ᵁ V)
  apply map_homotopy_counit_square
    (Scheme.Modules.tensorPullback f) (Scheme.Modules.pushforward f)
    (Scheme.Modules.tensorPullback (f ∣_ V)) (Scheme.Modules.pushforward (f ∣_ V))
    (schemeOpenRestriction Y V) (schemeOpenRestriction X (f ⁻¹ᵁ V))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V)))
    (openPinnedTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V) (morphismRestrict_ι f V))
    (singleComplexOpenUnderivedDirectImageIso f V)
  intro M
  have h := mateEquiv_counit
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V)))
    (TwoSquare.mk _ _ _ _
      (openPinnedTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
        (morphismRestrict_ι f V)).inv) M
  have hm := singleComplexOpen_underived_tensor_mate f V
  exact h.symm.trans (congrArg
    (fun z ↦ (Scheme.Modules.tensorPullback (f ∣_ V)).map z ≫
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ∣_ V))).counit.app
        ((schemeOpenRestriction X (f ⁻¹ᵁ V)).obj M)) (congr_app hm M))

end AlgebraicGeometry
