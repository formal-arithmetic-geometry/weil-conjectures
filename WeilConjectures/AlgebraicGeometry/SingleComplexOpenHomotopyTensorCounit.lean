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

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-homotopy-tensor-counit).
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

end AlgebraicGeometry
