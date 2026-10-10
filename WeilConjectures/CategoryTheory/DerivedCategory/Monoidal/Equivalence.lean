/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.HomotopyCategory.OplaxMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Monoidal equivalences and the derived tensor product

Let `E : C ≌ D` be an equivalence of monoidal Grothendieck abelian categories with functorial
flat resolutions, whose functor is monoidal. The induced equivalence `D(E) : D(C) ≌ D(D)` of
derived categories is compatible with the derived tensor products and with duals:

`D(E)(K ⊗ᴸ L) ≅ D(E)(K) ⊗ᴸ D(E)(L)` and `D(E)(RHom(K, 𝟙)) ≅ RHom(D(E)(K), 𝟙)`.

Both sides of the first isomorphism are computed on a K-flat representative of `K`, which `E`
carries to a K-flat complex. The second follows from the first by uniqueness of right adjoints.

## Main results

- `CategoryTheory.Equivalence.kFlat_mapHomotopyCategory_obj`: `E` preserves K-flat complexes.
- `CategoryTheory.Equivalence.nonempty_tensorLeft_comp_mapDerivedCategory_iso`:
  `D(E)(K ⊗ᴸ -) ≅ D(E)(K) ⊗ᴸ D(E)(-)`.
- `CategoryTheory.Equivalence.mapDerivedCategoryObjUnitIso`: `D(E)(𝟙) ≅ 𝟙`.
- `CategoryTheory.Equivalence.nonempty_mapDerivedCategory_obj_ihom_obj_unit_iso`:
  `D(E)(RHom(K, 𝟙)) ≅ RHom(D(E)(K), 𝟙)`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory DerivedCategory

universe w v u u₁ u₂

namespace HomotopyCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object of the homotopy category is acyclic if and only if its image in the derived
category is zero. -/
lemma subcategoryAcyclic_iff_isZero_Qh_obj (Z : HomotopyCategory C (.up ℤ)) :
    subcategoryAcyclic C Z ↔ IsZero (Qh.obj Z) := by
  rw [mem_subcategoryAcyclic_iff, DerivedCategory.isZero_iff]
  exact forall_congr' fun n ↦ ((homologyFunctorFactorsh C n).app Z).isZero_iff.symm

variable {D : Type*} [Category D] [Abelian D] [HasDerivedCategory.{w} D]

/-- An exact functor carries acyclic complexes to acyclic complexes. -/
lemma subcategoryAcyclic_mapHomotopyCategory_obj (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {Z : HomotopyCategory C (.up ℤ)}
    (hZ : subcategoryAcyclic C Z) :
    subcategoryAcyclic D ((F.mapHomotopyCategory (.up ℤ)).obj Z) := by
  rw [subcategoryAcyclic_iff_isZero_Qh_obj] at hZ ⊢
  exact (F.mapDerivedCategory.map_isZero hZ).of_iso (F.mapDerivedCategoryFactorsh.app Z).symm

end HomotopyCategory

namespace CategoryTheory.Equivalence

open HomotopyCategory Functor.OplaxMonoidal

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{v} C] [IsGrothendieckAbelian.{v} D]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalPreadditive C] [MonoidalPreadditive D]
  [MonoidalClosed C] [MonoidalClosed D] [BraidedCategory C] [BraidedCategory D]
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v} D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  (E : C ≌ D) [E.functor.Additive] [E.inverse.Additive] [E.functor.Monoidal]

omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D] in
/-- A monoidal equivalence of abelian categories carries K-flat complexes to K-flat
complexes. -/
lemma kFlat_mapHomotopyCategory_obj {P : HomotopyCategory C (.up ℤ)}
    (hP : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat P) :
    (HomotopyCategory.quasiIso D (.up ℤ)).kFlat
      ((E.functor.mapHomotopyCategory (.up ℤ)).obj P) := by
  rw [kFlat_iff_preserves_acyclic] at hP ⊢
  intro Z hZ
  obtain ⟨K, rfl⟩ := Z.quotient_obj_surjective
  let Z' := (quotient C (.up ℤ)).obj ((E.inverse.mapHomologicalComplex _).obj K)
  have hZ' : subcategoryAcyclic C Z' := subcategoryAcyclic_mapHomotopyCategory_obj E.inverse hZ
  let e : (quotient D _).obj K ≅ (E.functor.mapHomotopyCategory _).obj Z' :=
    (quotient D _).mapIso ((E.mapHomologicalComplex (.up ℤ)).counitIso.app K).symm
  let δ := asIso (mapHomotopyCategoryδNatTrans (.up ℤ) E.functor)
  constructor
  · exact (subcategoryAcyclic D).prop_of_iso ((δ.app P).app Z' ≪≫ whiskerLeftIso _ e.symm)
      (subcategoryAcyclic_mapHomotopyCategory_obj E.functor (hP Z' hZ').1)
  · exact (subcategoryAcyclic D).prop_of_iso ((δ.app Z').app P ≪≫ whiskerRightIso e.symm _)
      (subcategoryAcyclic_mapHomotopyCategory_obj E.functor (hP Z' hZ').2)

/-- For a K-flat complex `P`, the derived functor of a monoidal equivalence `E` commutes with
`Qh.obj P ⊗ᴸ -`: `D(E)(Qh P ⊗ᴸ K) ≅ D(E)(Qh P) ⊗ᴸ D(E)(K)`, naturally in `K`. -/
lemma nonempty_tensorLeft_Qh_obj_comp_mapDerivedCategory_iso {P : HomotopyCategory C (.up ℤ)}
    (hP : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat P) :
    Nonempty ((curriedTensor (DerivedCategory C)).obj (Qh.obj P) ⋙
        E.functor.mapDerivedCategory ≅
      E.functor.mapDerivedCategory ⋙ (curriedTensor (DerivedCategory D)).obj
        (E.functor.mapDerivedCategory.obj (Qh.obj P))) := by
  let F := E.functor.mapDerivedCategory
  let EK := E.functor.mapHomotopyCategory (.up ℤ)
  have hP' := E.kFlat_mapHomotopyCategory_obj hP
  have := isIso_tensorLeftCounit P hP
  have := isIso_tensorLeftCounit (EK.obj P) hP'
  let δ := asIso (mapHomotopyCategoryδNatTrans (.up ℤ) E.functor)
  let e₁ : Qh ⋙ ((curriedTensor _).obj (Qh.obj P) ⋙ F) ≅
      Qh ⋙ (F ⋙ (curriedTensor _).obj (F.obj (Qh.obj P))) :=
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (asIso (tensorLeftCounit P)) F ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ E.functor.mapDerivedCategoryFactorsh ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (δ.app P) Qh ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft EK (asIso (tensorLeftCounit (EK.obj P))).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.functor.mapDerivedCategoryFactorsh.symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft Qh (Functor.isoWhiskerLeft F
        ((curriedTensor _).mapIso (E.functor.mapDerivedCategoryFactorsh.app P).symm))
  exact ⟨(Localization.whiskeringLeftFunctor' Qh (HomotopyCategory.quasiIso C (.up ℤ))
    (DerivedCategory D)).preimageIso e₁⟩

/-- The derived functor of a monoidal equivalence `E` commutes with `K ⊗ᴸ -`:
`D(E)(K ⊗ᴸ L) ≅ D(E)(K) ⊗ᴸ D(E)(L)`, naturally in `L`. -/
lemma nonempty_tensorLeft_comp_mapDerivedCategory_iso (K : DerivedCategory C) :
    Nonempty ((curriedTensor (DerivedCategory C)).obj K ⋙ E.functor.mapDerivedCategory ≅
      E.functor.mapDerivedCategory ⋙ (curriedTensor (DerivedCategory D)).obj
        (E.functor.mapDerivedCategory.obj K)) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := DerivedCategory.exists_kFlat_iso K
  obtain ⟨τ⟩ := E.nonempty_tensorLeft_Qh_obj_comp_mapDerivedCategory_iso hP
  exact ⟨Functor.isoWhiskerRight ((curriedTensor _).mapIso e.symm) _ ≪≫ τ ≪≫
    Functor.isoWhiskerLeft _ ((curriedTensor _).mapIso (E.functor.mapDerivedCategory.mapIso e))⟩

/-- The derived functor of a monoidal equivalence `E` preserves the monoidal unit. -/
noncomputable def mapDerivedCategoryObjUnitIso :
    E.functor.mapDerivedCategory.obj (𝟙_ (DerivedCategory C)) ≅ 𝟙_ (DerivedCategory D) :=
  E.functor.mapDerivedCategory.mapIso (DerivedCategory.singleFunctorObjUnitIso C).symm ≪≫
    (E.functor.mapDerivedCategorySingleFunctor 0).app (𝟙_ C) ≪≫
    (DerivedCategory.singleFunctor D 0).mapIso (Functor.Monoidal.εIso E.functor).symm ≪≫
    DerivedCategory.singleFunctorObjUnitIso D

/-- The derived functor of a monoidal equivalence `E` commutes with duals:
`D(E)(RHom(K, 𝟙)) ≅ RHom(D(E)(K), 𝟙)`. -/
theorem nonempty_mapDerivedCategory_obj_ihom_obj_unit_iso (K : DerivedCategory C) :
    Nonempty (E.functor.mapDerivedCategory.obj ((ihom K).obj (𝟙_ _)) ≅
      (ihom (E.functor.mapDerivedCategory.obj K)).obj (𝟙_ _)) := by
  let 𝔼 := E.mapDerivedCategory
  obtain ⟨τ⟩ := E.nonempty_tensorLeft_comp_mapDerivedCategory_iso K
  let adj := 𝔼.symm.toAdjunction.comp ((ihom.adjunction K).comp 𝔼.toAdjunction)
  let iso : 𝔼.inverse ⋙ (tensorLeft K ⋙ 𝔼.functor) ≅
      tensorLeft (E.functor.mapDerivedCategory.obj K) :=
    Functor.isoWhiskerLeft _ τ ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight 𝔼.counitIso _ ≪≫ Functor.leftUnitor _
  let u : 𝔼.inverse.obj (𝟙_ (DerivedCategory D)) ≅ 𝟙_ (DerivedCategory C) :=
    𝔼.inverse.mapIso (E.mapDerivedCategoryObjUnitIso).symm ≪≫ 𝔼.unitIso.symm.app _
  exact ⟨E.functor.mapDerivedCategory.mapIso ((ihom K).mapIso u.symm) ≪≫
    (((ihom.adjunction _).rightAdjointUniq (adj.ofNatIsoLeft iso)).app _).symm⟩

end CategoryTheory.Equivalence

end
