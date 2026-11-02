/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-! # Comparison of two reduction functors computed on a common resolving class

Source: Stacks Tags 05SE and 06YY (auxiliary; not a blueprint node).

Two composites of a left derived functor with an exact functor, whose counits become
invertible on a common resolving class and whose underlying additive functors are identified,
are isomorphic, compatibly with the counits read on complexes of the class. This is the
abstract input for the strict reduction comparison `rho` of the ordered exchange.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Two functors on the derived category with counits to the same exact homotopy functor,
invertible on a resolving class, are isomorphic compatibly with the counits.
Source: Stacks Tag 05SE (auxiliary; not a blueprint node). -/
theorem leftDerived_normalized_iso
    {B C : Type*} [Category B] [Abelian B] [HasDerivedCategory B]
    [Category C] [Abelian C] [HasDerivedCategory C]
    (E : B ⥤ C) [E.Additive] (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (p : P ⟶ X), S P ∧ QuasiIso p)
    (hinv : ∀ {P Q : CochainComplex B ℤ} (a : P ⟶ Q), S P → S Q → QuasiIso a →
      QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map a))
    (F₁ F₂ : DerivedCategory B ⥤ DerivedCategory C)
    (a₁ : DerivedCategory.Qh ⋙ F₁ ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (a₂ : DerivedCategory.Qh ⋙ F₂ ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (h₁ : ∀ P, S P → IsIso (a₁.app ((HomotopyCategory.quotient B (.up ℤ)).obj P)))
    (h₂ : ∀ P, S P → IsIso (a₂.app ((HomotopyCategory.quotient B (.up ℤ)).obj P))) :
    ∃ e : F₁ ≅ F₂, ∀ X, e.hom.app (DerivedCategory.Qh.obj X) ≫ a₂.app X = a₁.app X := by
  obtain ⟨LF, ε, hLF, -, hε⟩ := derivedPair_from_complex_resolutions E S hres hinv
  let W := HomotopyCategory.quasiIso B (.up ℤ)
  let τ₁ := LF.leftDerivedLift ε W F₁ a₁
  let τ₂ := LF.leftDerivedLift ε W F₂ a₂
  have hτ₁ (X) : τ₁.app (DerivedCategory.Qh.obj X) ≫ ε.app X = a₁.app X :=
    LF.leftDerived_fac_app ε W F₁ a₁ X
  have hτ₂ (X) : τ₂.app (DerivedCategory.Qh.obj X) ≫ ε.app X = a₂.app X :=
    LF.leftDerived_fac_app ε W F₂ a₂ X
  have key (G : DerivedCategory B ⥤ DerivedCategory C) (τ : G ⟶ LF)
      (a : DerivedCategory.Qh ⋙ G ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
      (ha : ∀ P, S P → IsIso (a.app ((HomotopyCategory.quotient B (.up ℤ)).obj P)))
      (hτ : ∀ X, τ.app (DerivedCategory.Qh.obj X) ≫ ε.app X = a.app X) : IsIso τ := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro K
    obtain ⟨P, p, hP, hp⟩ := hres (DerivedCategory.Q.objPreimage K)
    have := hp
    let X := (HomotopyCategory.quotient B (.up ℤ)).obj P
    let i : DerivedCategory.Qh.obj X ≅ K :=
      asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
    have := hε P hP
    have := ha P hP
    have : IsIso (τ.app (DerivedCategory.Qh.obj X)) := by
      have : IsIso (τ.app (DerivedCategory.Qh.obj X) ≫ ε.app X) := by
        rw [hτ X]
        infer_instance
      exact IsIso.of_isIso_comp_right _ (ε.app X)
    exact (NatTrans.isIso_app_iff_of_iso τ i).mp this
  have : IsIso τ₁ := key F₁ τ₁ a₁ h₁ hτ₁
  have : IsIso τ₂ := key F₂ τ₂ a₂ h₂ hτ₂
  refine ⟨asIso τ₁ ≪≫ (asIso τ₂).symm, fun X ↦ ?_⟩
  simp only [Iso.trans_hom, asIso_hom, Iso.symm_hom, asIso_inv, NatTrans.comp_app,
    Category.assoc]
  rw [← hτ₂, ← hτ₁]
  simp


private theorem factorsh_hom_quotient' {B E : Type*} [Category B] [Category E]
    [Abelian B] [Abelian E] [HasDerivedCategory B] [HasDerivedCategory E]
    (F : B ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : CochainComplex B ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K) =
      F.mapDerivedCategoryFactors.hom.app K := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  have h1 : (DerivedCategory.quotientCompQhIso B).hom.app K = 𝟙 _ := rfl
  have h2 : (DerivedCategory.quotientCompQhIso E).inv.app
      ((F.mapHomologicalComplex (.up ℤ)).obj K) = 𝟙 _ := rfl
  have h3 : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  rw [h1, h2, h3]
  simp

section Composite

variable {B B' C C' : Type*} [Category B] [Category B'] [Category C] [Category C']
  {_ : Abelian B} {_ : Abelian B'} {_ : Abelian C} {_ : Abelian C'}
  {_ : HasDerivedCategory B} {_ : HasDerivedCategory B'} {_ : HasDerivedCategory C}
  {_ : HasDerivedCategory C'}
  (r : B ⥤ B') [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  (tr : C' ⥤ C) [tr.Additive] [PreservesFiniteLimits tr] [PreservesFiniteColimits tr]
  (M : B ⥤ C') [M.Additive] (N : B' ⥤ C) [N.Additive]
  (L₁ : DerivedCategory B ⥤ DerivedCategory C')
  (ε₁ : DerivedCategory.Qh ⋙ L₁ ⟶ M.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
  (L₂ : DerivedCategory B' ⥤ DerivedCategory C)
  (ε₂ : DerivedCategory.Qh ⋙ L₂ ⟶ N.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)

/-- The counit of the exact functor followed by the second reduction. -/
private def secondCounit :
    DerivedCategory.Qh ⋙ (r.mapDerivedCategory ⋙ L₂) ⟶
      (r ⋙ N).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight r.mapDerivedCategoryFactorsh.hom L₂ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (r.mapHomotopyCategory (.up ℤ)) ε₂ ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (r ⋙ N)) (.up ℤ)).hom
      DerivedCategory.Qh

/-- The counit of the first reduction followed by the exact functor, transported by `ρ`. -/
private def firstCounit (ρ : r ⋙ N ≅ M ⋙ tr) :
    DerivedCategory.Qh ⋙ (L₁ ⋙ tr.mapDerivedCategory) ⟶
      (r ⋙ N).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ε₁ tr.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (M.mapHomotopyCategory (.up ℤ)) tr.mapDerivedCategoryFactorsh.hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso (Iso.refl (M ⋙ tr)) (.up ℤ)).hom
      DerivedCategory.Qh ≫
    Functor.whiskerRight (NatTrans.mapHomotopyCategory ρ.inv (.up ℤ)) DerivedCategory.Qh

private theorem secondCounit_quotient (P : CochainComplex B ℤ) :
    (secondCounit r N L₂ ε₂).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      L₂.map (r.mapDerivedCategoryFactors.hom.app P) ≫
        reductionComplexCounit N L₂ ε₂ ((r.mapHomologicalComplex (.up ℤ)).obj P) := by
  simp only [secondCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  rw [factorsh_hom_quotient']
  unfold reductionComplexCounit
  have h1 : (DerivedCategory.quotientCompQhIso B').inv.app
      ((r.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  have h2 : (N.mapHomotopyCategoryFactors (.up ℤ)).hom.app
      ((r.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  have h3 : (DerivedCategory.quotientCompQhIso C).hom.app
      ((N.mapHomologicalComplex (.up ℤ)).obj ((r.mapHomologicalComplex (.up ℤ)).obj P)) =
        𝟙 _ := rfl
  rw [h1, h2, h3]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.comp_id]
  rfl

omit [PreservesFiniteLimits r] [PreservesFiniteColimits r] in
private theorem firstCounit_quotient (ρ : r ⋙ N ≅ M ⋙ tr) (P : CochainComplex B ℤ) :
    (firstCounit r tr M N L₁ ε₁ ρ).app ((HomotopyCategory.quotient _ (.up ℤ)).obj P) =
      tr.mapDerivedCategory.map (reductionComplexCounit M L₁ ε₁ P) ≫
        tr.mapDerivedCategoryFactors.hom.app ((M.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ρ.symm (.up ℤ)).hom.app P) := by
  simp only [firstCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  erw [factorsh_hom_quotient' tr ((M.mapHomologicalComplex (.up ℤ)).obj P)]
  unfold reductionComplexCounit
  have h1 : (DerivedCategory.quotientCompQhIso B).inv.app P = 𝟙 _ := rfl
  have h2 : (M.mapHomotopyCategoryFactors (.up ℤ)).hom.app P = 𝟙 _ := rfl
  have h3 : (DerivedCategory.quotientCompQhIso C').hom.app
      ((M.mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  rw [h1, h2, h3]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  repeat erw [CategoryTheory.Functor.map_id]
  repeat erw [Category.comp_id]
  repeat erw [Category.id_comp]
  rfl

/-- Two reduction composites agreeing on underlying additive functors are isomorphic,
compatibly with their counits on the resolving class.
Source: Stacks Tags 05SE and 06YY (auxiliary; not a blueprint node). -/
theorem reductionComposite_normalized_iso (ρ : r ⋙ N ≅ M ⋙ tr)
    (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (p : P ⟶ X), S P ∧ QuasiIso p)
    (hinv : ∀ {P Q : CochainComplex B ℤ} (a : P ⟶ Q), S P → S Q → QuasiIso a →
      QuasiIso (((r ⋙ N).mapHomologicalComplex (.up ℤ)).map a))
    (h₁ : ∀ P, S P → IsIso (ε₁.app ((HomotopyCategory.quotient B (.up ℤ)).obj P)))
    (h₂ : ∀ P, S P → IsIso (ε₂.app ((HomotopyCategory.quotient B' (.up ℤ)).obj
      ((r.mapHomologicalComplex (.up ℤ)).obj P)))) :
    ∃ e : L₁ ⋙ tr.mapDerivedCategory ≅ r.mapDerivedCategory ⋙ L₂,
      ∀ P, S P →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            L₂.map (r.mapDerivedCategoryFactors.hom.app P) ≫
            reductionComplexCounit N L₂ ε₂ ((r.mapHomologicalComplex (.up ℤ)).obj P) =
          tr.mapDerivedCategory.map (reductionComplexCounit M L₁ ε₁ P) ≫
            tr.mapDerivedCategoryFactors.hom.app ((M.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ρ.symm (.up ℤ)).hom.app P) := by
  obtain ⟨e, he⟩ := leftDerived_normalized_iso (r ⋙ N) S hres hinv _ _
    (firstCounit r tr M N L₁ ε₁ ρ) (secondCounit r N L₂ ε₂)
    (fun P hP ↦ by
      have := h₁ P hP
      rw [firstCounit_quotient]
      have : IsIso ((NatIso.mapHomologicalComplex ρ.symm (.up ℤ)).hom.app P) := inferInstance
      unfold reductionComplexCounit
      infer_instance)
    (fun P hP ↦ by
      have := h₂ P hP
      rw [secondCounit_quotient]
      unfold reductionComplexCounit
      infer_instance)
  refine ⟨e, fun P _ ↦ ?_⟩
  rw [← secondCounit_quotient, ← firstCounit_quotient]
  exact he _


/-- The comparison of `reductionComposite_normalized_iso`, with the second reduction given by
its universal model data.
Source: Stacks Tags 05SE and 06YY (auxiliary; not a blueprint node). -/
theorem reductionComposite_normalized_iso_of_data (ρ : r ⋙ N ≅ M ⋙ tr)
    {S₂ : CochainComplex B' ℤ → Prop} (D₂ : DerivedReductionModelData N S₂)
    (S : CochainComplex B ℤ → Prop)
    (hres : ∀ X : CochainComplex B ℤ, ∃ (P : CochainComplex B ℤ) (p : P ⟶ X), S P ∧ QuasiIso p)
    (hinv : ∀ {P Q : CochainComplex B ℤ} (a : P ⟶ Q), S P → S Q → QuasiIso a →
      QuasiIso (((r ⋙ N).mapHomologicalComplex (.up ℤ)).map a))
    (h₁ : ∀ P, S P → IsIso (ε₁.app ((HomotopyCategory.quotient B (.up ℤ)).obj P)))
    (h₂ : ∀ P, S P → S₂ ((r.mapHomologicalComplex (.up ℤ)).obj P)) :
    ∃ e : L₁ ⋙ tr.mapDerivedCategory ≅ r.mapDerivedCategory ⋙ D₂.reduction,
      ∀ P, S P →
        e.hom.app (DerivedCategory.Q.obj P) ≫
            D₂.reduction.map (r.mapDerivedCategoryFactors.hom.app P) ≫
            D₂.complexCounit ((r.mapHomologicalComplex (.up ℤ)).obj P) =
          tr.mapDerivedCategory.map (reductionComplexCounit M L₁ ε₁ P) ≫
            tr.mapDerivedCategoryFactors.hom.app ((M.mapHomologicalComplex (.up ℤ)).obj P) ≫
            DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ρ.symm (.up ℤ)).hom.app P) :=
  reductionComposite_normalized_iso r tr M N L₁ ε₁ D₂.reduction D₂.counit ρ S hres hinv h₁
    (fun P hP ↦ D₂.isIso_counit _ (h₂ P hP))

end Composite

end AlgebraicGeometry.Scheme
