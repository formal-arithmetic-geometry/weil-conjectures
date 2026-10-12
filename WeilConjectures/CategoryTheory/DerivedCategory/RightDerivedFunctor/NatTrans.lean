/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Functoriality of total right derived functors in natural transformations

For additive functors `F G : C ⥤ D` between abelian categories, where `C` has K-injective
resolutions, a natural transformation `τ : F ⟶ G` induces
`Functor.rightDerivedFunctorNatTrans τ : RF ⟶ RG`. This file records that this construction is
functorial (`Functor.rightDerivedFunctorNatTrans_id`, `Functor.rightDerivedFunctorNatTrans_comp`)
and computes it on K-injective complexes: under the isomorphisms `RF (Q I) ≅ Q (F I)` of
`Functor.rightDerivedFunctorObjQIso`, it is `Q` applied to the termwise map `F I ⟶ G I`
(`Functor.rightDerivedFunctorNatTrans_app_Q_obj`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]

@[simp]
lemma rightDerivedFunctorNatTrans_id (F : C ⥤ D) [F.Additive] :
    rightDerivedFunctorNatTrans (𝟙 F) = 𝟙 _ := by
  simp [rightDerivedFunctorNatTrans]

@[reassoc]
lemma rightDerivedFunctorNatTrans_comp {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (τ : F ⟶ G) (τ' : G ⟶ H) :
    rightDerivedFunctorNatTrans (τ ≫ τ') =
      rightDerivedFunctorNatTrans τ ≫ rightDerivedFunctorNatTrans τ' := by
  simp [rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory_comp]

/-- The natural transformation `RF ⟶ RG` induced by `τ : F ⟶ G` is computed on a K-injective
complex `I` by the termwise map `F I ⟶ G I`. -/
lemma rightDerivedFunctorNatTrans_app_Q_obj {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) (I : CochainComplex C ℤ) [I.IsKInjective] :
    (rightDerivedFunctorNatTrans τ).app (DerivedCategory.Q.obj I) =
      (F.rightDerivedFunctorObjQIso I).hom ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ _).app I) ≫
          (G.rightDerivedFunctorObjQIso I).inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  have h₁ := rightDerivedNatTrans_app F.rightDerivedFunctor G.rightDerivedFunctor
    F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ))
      DerivedCategory.Qh) ((HomotopyCategory.quotient _ _).obj I)
  have h₂ := (rightDerivedFunctorNatTrans τ).naturality
    ((DerivedCategory.quotientCompQhIso C).app I).inv
  simp only [rightDerivedFunctorObjQIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    asIso_inv, Category.assoc]
  erw [← reassoc_of% h₂]
  congr 1
  rw [← cancel_epi (F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)),
    IsIso.hom_inv_id_assoc]
  erw [reassoc_of% h₁]
  rw [IsIso.hom_inv_id_assoc]
  exact DerivedCategory.quotientCompQhIso_hom_naturality _

end CategoryTheory.Functor
