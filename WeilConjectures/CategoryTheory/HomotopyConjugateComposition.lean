/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
/-! # Conjugates and composition on homotopy categories -/
@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory
namespace CategoryTheory
/-- Inducing additive functors on homotopy categories preserves the conjugate of a
comparison with a composite right adjoint.
Source: degreewise adjunction units (blueprint: lem-sf-homotopy-conjugate-composition).
Proof: take the transpose under the composite adjunction, express each object as the
image of a complex, and use the ordinary conjugate unit identity degree by degree. -/
theorem homotopyConjugateComp
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    [CategoryTheory.Limits.HasBinaryBiproducts C]
    [CategoryTheory.Limits.HasBinaryBiproducts D]
    [CategoryTheory.Limits.HasBinaryBiproducts E]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ E} {S : E ⥤ D}
    {H : C ⥤ E} {T : E ⥤ C}
    [F.Additive] [R.Additive] [G.Additive] [S.Additive] [H.Additive] [T.Additive]
    (a : F ⊣ R) (b : G ⊣ S) (h : H ⊣ T) (r : T ≅ S ⋙ R)
    (P : HomotopyCategory C (.up ℤ)) :
    ((conjugateEquiv (h.mapHomotopyCategory (.up ℤ))
      ((a.mapHomotopyCategory (.up ℤ)).comp (b.mapHomotopyCategory (.up ℤ)))).symm
      (Functor.mapHomotopyCategoryCompIso r.symm (.up ℤ)).inv).app P =
    (Functor.mapHomotopyCategoryCompIso
      ((conjugateIsoEquiv h (a.comp b)).symm r) (.up ℤ)).hom.app P := by
  apply (((a.mapHomotopyCategory (.up ℤ)).comp
    (b.mapHomotopyCategory (.up ℤ))).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [← unit_conjugateEquiv_symm]
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  rw [Adjunction.comp_unit_app, Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_unit_app_quotient]
  have hb : (b.mapHomotopyCategory (.up ℤ)).unit.app
      ((F.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient C (.up ℤ)).obj P)) =
      (HomotopyCategory.quotient D (.up ℤ)).map
        ((b.mapHomologicalComplex (.up ℤ)).unit.app
          ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    Adjunction.mapHomotopyCategory_unit_app_quotient _ b _
  rw [hb]
  change (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ =
    ((HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _) ≫
        (HomotopyCategory.quotient C (.up ℤ)).map _
  simp only [← Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.symm_inv,
    HomotopyCategory.quotient_obj_as]
  change h.unit.app (P.X n) ≫ r.hom.app (H.obj (P.X n)) =
    (a.unit.app (P.X n) ≫ R.map (b.unit.app (F.obj (P.X n)))) ≫
      R.map (S.map (((conjugateEquiv h (a.comp b)).symm r.hom).app (P.X n)))
  simpa only [Adjunction.comp_unit_app, Functor.comp_map] using
    unit_conjugateEquiv_symm h (a.comp b) r.hom (P.X n)
end CategoryTheory
