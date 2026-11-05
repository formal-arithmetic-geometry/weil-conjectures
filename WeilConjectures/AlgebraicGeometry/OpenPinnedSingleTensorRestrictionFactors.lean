/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso

/-! # Single-complex identities for exact restriction and tensor reassociation
Source: Stacks Project, Tags 08DW and 08HY; Mathlib exact single comparison.
(blueprint: lem-pc-open-pinned-single-tensor-restriction-factors). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

private lemma complex_single_square
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E] (F : C ⥤ D) (G : D ⥤ E)
    (R : C ⥤ B) (J : B ⥤ E)
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    (e : F ⋙ G ≅ R ⋙ J) (M : C) :
    (G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M) ≫
      (HomologicalComplex.single E (.up ℤ) 0).map (e.hom.app M) =
    (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app
        ((HomologicalComplex.single C (.up ℤ) 0).obj M) ≫
      (J.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex J (.up ℤ) 0).hom.app (R.obj M) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases h : i = 0
  · subst i
    simp only [HomologicalComplex.single, Functor.comp_obj, ↓dreduceIte,
      HomologicalComplex.singleMapHomologicalComplex, NatIso.ofComponents_hom_app,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, ↓reduceDIte,
      eqToHom_refl, Category.comp_id, Category.id_comp,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      NatTrans.mapHomologicalComplex]
    erw [G.map_id, J.map_id]
    change 𝟙 (G.obj (F.obj M)) ≫ e.hom.app M =
      e.hom.app M ≫ 𝟙 (J.obj (R.obj M))
    erw [Category.id_comp, Category.comp_id]
  · simp [HomologicalComplex.singleMapHomologicalComplex, h]

private lemma homotopy_single_square
    {C D B E : Type*} [Category C] [Category D] [Category B] [Category E]
    [Abelian C] [Abelian D] [Abelian B] [Abelian E] (F : C ⥤ D) (G : D ⥤ E)
    (R : C ⥤ B) (J : B ⥤ E)
    [F.Additive] [G.Additive] [R.Additive] [J.Additive]
    (e : F ⋙ G ≅ R ⋙ J) (M : C) :
    (G.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M)) ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.single E (.up ℤ) 0).map (e.hom.app M)) =
    ((Functor.mapHomotopyCategoryCompIso e (.up ℤ)) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ J)) (.up ℤ)).symm).hom.app
        ((HomotopyCategory.singleFunctor C 0).obj M) ≫
      (J.mapHomotopyCategory (.up ℤ)).map
        ((HomotopyCategory.quotient _ (.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app M)) ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex J (.up ℤ) 0).hom.app (R.obj M)) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    Functor.mapHomotopyCategory_map]
  change (HomotopyCategory.quotient E (.up ℤ)).map
      ((G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M)) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M)) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((HomologicalComplex.single E (.up ℤ) 0).map (e.hom.app M)) =
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom.app
        ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map (𝟙 _) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((J.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex R (.up ℤ) 0).hom.app M)) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex J (.up ℤ) 0).hom.app (R.obj M))
  simp only [Category.id_comp, ← Functor.map_comp]
  exact congrArg (HomotopyCategory.quotient E (.up ℤ)).map
    (complex_single_square F G R J e M)

end AlgebraicGeometry
