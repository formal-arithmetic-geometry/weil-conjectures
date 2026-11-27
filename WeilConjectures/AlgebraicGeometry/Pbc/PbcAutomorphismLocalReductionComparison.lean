/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleCompleteSupplement
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismLocalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedPullbackComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import all WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerPullbackSupplement
import all WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicRestrictedTower
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcAutomorphismLocalComplex
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcFinitePullbackConstructibility
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition

/-! Reduction transitions under inverse image and coefficient relabelling.

The transitions of a finite reduction system are adjuncts of scalar-extension units.
They commute with every mate of a compatible family of restriction squares; this applies
to exact inverse image and to restriction along coefficient isomorphisms.

## References

* Stacks Tags 06YY and 0D6D
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Adjuncts of composite units commute with the mates of a compatible family of squares
of right adjoints. -/
theorem homEquiv_symm_unit_mateEquiv_symm
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    {L₁ : C₀ ⥤ C₁} {R₁ : C₁ ⥤ C₀} {L₂ : C₀ ⥤ C₂} {R₂ : C₂ ⥤ C₀} {Rb : C₂ ⥤ C₁}
    {L₁' : D₀ ⥤ D₁} {R₁' : D₁ ⥤ D₀} {L₂' : D₀ ⥤ D₂} {R₂' : D₂ ⥤ D₀} {Rb' : D₂ ⥤ D₁}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
    (γ : Rb ⋙ R₁ ≅ R₂) (γ' : Rb' ⋙ R₁' ≅ R₂')
    {F₀ : C₀ ⥤ D₀} {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂}
    (σ₁ : R₁ ⋙ F₀ ⟶ F₁ ⋙ R₁') (σ₂ : R₂ ⋙ F₀ ⟶ F₂ ⋙ R₂') (σb : Rb ⋙ F₁ ⟶ F₂ ⋙ Rb')
    (K : C₀)
    (hσ : F₀.map (γ.hom.app (L₂.obj K)) ≫ σ₂.app (L₂.obj K) =
      σ₁.app (Rb.obj (L₂.obj K)) ≫ R₁'.map (σb.app (L₂.obj K)) ≫
        γ'.hom.app (F₂.obj (L₂.obj K))) :
    ((mateEquiv adj₁ adj₁').symm σ₁).app K ≫
        F₁.map ((adj₁.homEquiv _ _).symm (adj₂.unit.app K ≫ γ.inv.app (L₂.obj K))) ≫
        σb.app (L₂.obj K) =
      (adj₁'.homEquiv _ _).symm
          (adj₂'.unit.app (F₀.obj K) ≫ γ'.inv.app (L₂'.obj (F₀.obj K))) ≫
        Rb'.map (((mateEquiv adj₂ adj₂').symm σ₂).app K) := by
  have h₁ := unit_mateEquiv_symm adj₁ adj₁' σ₁ K
  have h₂ := unit_mateEquiv_symm adj₂ adj₂' σ₂ K
  have hT := adj₁.homEquiv_unit K _ ((adj₁.homEquiv _ _).symm
    (adj₂.unit.app K ≫ γ.inv.app (L₂.obj K)))
  rw [Equiv.apply_symm_apply] at hT
  have hT' := adj₁'.homEquiv_unit (F₀.obj K) _ ((adj₁'.homEquiv _ _).symm
    (adj₂'.unit.app (F₀.obj K) ≫ γ'.inv.app (L₂'.obj (F₀.obj K))))
  rw [Equiv.apply_symm_apply] at hT'
  have hn := σ₁.naturality
    ((adj₁.homEquiv _ _).symm (adj₂.unit.app K ≫ γ.inv.app (L₂.obj K)))
  have hγ := γ'.inv.naturality (((mateEquiv adj₂ adj₂').symm σ₂).app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at h₁ h₂ hn hT hT' hγ ⊢
  apply (adj₁'.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [← h₁]
  simp only [Category.assoc]
  rw [← reassoc_of% hn, ← F₀.map_comp_assoc, ← hT, ← reassoc_of% hT', ← hγ,
    ← reassoc_of% h₂, F₀.map_comp_assoc]
  congr 1
  rw [← cancel_epi (F₀.map (γ.hom.app (L₂.obj K))), ← F₀.map_comp_assoc,
    Iso.hom_inv_id_app, F₀.map_id, Category.id_comp, reassoc_of% hσ, Iso.hom_inv_id_app]
  simp

/-- The inverse mate of an isomorphism of right adjoints along equivalences is invertible. -/
theorem isIso_mateEquiv_symm_of_equivalence
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (eG : A ≌ C) (eH : B ≌ D)
    (σ : R₁ ⋙ eG.functor ≅ eH.functor ⋙ R₂) :
    IsIso ((mateEquiv adj₁ adj₂).symm σ.hom) := by
  have h := iterated_mateEquiv_conjugateEquiv_symm adj₁ adj₂ eG.toAdjunction eH.toAdjunction
    (mateEquiv eH.toAdjunction eG.toAdjunction σ.hom)
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  have : IsIso (mateEquiv eH.toAdjunction eG.toAdjunction σ.hom) := by
    have (X : D) : IsIso ((mateEquiv eH.toAdjunction eG.toAdjunction σ.hom).app X) := by
      simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
        Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Equivalence.toAdjunction_unit,
        Equivalence.toAdjunction_counit, Functor.comp_obj, Functor.id_obj, Category.id_comp,
        Category.comp_id, Functor.comp_map]
      have : IsIso (σ.hom.app (eH.inverse.obj X)) := inferInstance
      have : IsIso (eG.unit.app (R₁.obj (eH.inverse.obj X))) := inferInstance
      have : IsIso (eH.counit.app X) := inferInstance
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  infer_instance

end CategoryTheory

namespace AlgebraicGeometry.Scheme

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Pullback

variable {Z U : Scheme.{u}} (h : U ⟶ Z)

/-- Derived scalar extension commutes with exact inverse image, with the inverse-image
coefficient sheaves. -/
def pbcPullbackExtendIso {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}} (a : R ⟶ S) :
    pbcDerivedExtend a ⋙ adicTowerPullback h S ≅
      adicTowerPullback h R ⋙ pbcDerivedExtend ((adicTowerInverseImage h).map a) :=
  proEtaleReductionPullbackIso h R S _ _ a ((adicTowerInverseImage h).map a)
    (Iso.refl _) (Iso.refl _) ((Category.id_comp _).trans (Category.comp_id _).symm)

private theorem pbcPullbackExtendIso_inv {R S : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}}
    (a : R ⟶ S) :
    (pbcPullbackExtendIso h a).inv =
      (mateEquiv (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction ((adicTowerInverseImage h).map a))).symm
        (scalarDerivedSquare h a).hom := by
  rw [scalarDerivedSquare_hom]
  rfl

/-- Inverse image carries the reduction transition to the reduction transition of the
inverse-image coefficient maps. -/
theorem pbcPullbackExtendIso_transition
    {R S B : Sheaf (ProEt.topology Z) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (hc : a ≫ b = c)
    (K : DerivedCategory (pbcModules Z R)) :
    (adicTowerPullback h S).map (pbcReductionTransition a b c hc K) ≫
        (proEtaleRingRestrictionDerivedPullback h S B _ _ b ((adicTowerInverseImage h).map b)
          (Iso.refl _) (Iso.refl _)
          ((Category.id_comp _).trans (Category.comp_id _).symm)).inv.app
            ((pbcDerivedExtend c).obj K) ≫
        (pbcDerivedRestrict ((adicTowerInverseImage h).map b)).map
          ((pbcPullbackExtendIso h c).hom.app K) =
      (pbcPullbackExtendIso h a).hom.app K ≫
        pbcReductionTransition ((adicTowerInverseImage h).map a)
          ((adicTowerInverseImage h).map b) ((adicTowerInverseImage h).map c)
          (by rw [← Functor.map_comp, hc]) ((adicTowerPullback h R).obj K) := by
  have key := homEquiv_symm_unit_mateEquiv_symm (pbcDerivedScalarAdjunction a)
    (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction ((adicTowerInverseImage h).map a))
    (pbcDerivedScalarAdjunction ((adicTowerInverseImage h).map c))
    (pbcDerivedRestrictComp a b c hc)
    (pbcDerivedRestrictComp ((adicTowerInverseImage h).map a)
      ((adicTowerInverseImage h).map b) ((adicTowerInverseImage h).map c)
      (by rw [← Functor.map_comp, hc]))
    (scalarDerivedSquare h a).hom (scalarDerivedSquare h c).hom (scalarDerivedSquare h b).hom K
    (scalarDerivedSquare_comp h a b c hc _)
  rw [← pbcPullbackExtendIso_inv, ← pbcPullbackExtendIso_inv, scalarDerivedSquare_hom] at key
  rw [← cancel_epi ((pbcPullbackExtendIso h a).inv.app K), Iso.inv_hom_id_app_assoc]
  have k₂ := key =≫ (pbcDerivedRestrict ((adicTowerInverseImage h).map b)).map
    ((pbcPullbackExtendIso h c).hom.app K)
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id, Functor.id_obj] at k₂
  exact k₂

end Pullback

section Relabel

variable {T : Scheme.{u}}

/-- Ordinary restriction along the two sides of a commutative square of coefficient maps. -/
def pbcRestrictSquare {R S R' S' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (ψ : R ⟶ R') (κ : S ⟶ S') (a : R ⟶ S) (a' : R' ⟶ S') (w : a ≫ κ = ψ ≫ a') :
    pbcRestrict a' ⋙ pbcRestrict ψ ≅ pbcRestrict κ ⋙ pbcRestrict a :=
  pbcRestrictComp ψ a' (ψ ≫ a') rfl ≪≫ (pbcRestrictComp a κ (ψ ≫ a') w).symm

/-- Derived restriction along the two sides of a commutative square of coefficient maps. -/
abbrev pbcDerivedRestrictSquare {R S R' S' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (ψ : R ⟶ R') (κ : S ⟶ S') (a : R ⟶ S) (a' : R' ⟶ S') (w : a ≫ κ = ψ ≫ a') :
    pbcDerivedRestrict a' ⋙ pbcDerivedRestrict ψ ≅
      pbcDerivedRestrict κ ⋙ pbcDerivedRestrict a :=
  Functor.mapDerivedCategorySquareIso (pbcRestrictSquare ψ κ a a' w)

private theorem pbcRestrictSquare_hom_apply
    {R S R' S' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (ψ : R ⟶ R') (κ : S ⟶ S') (a : R ⟶ S) (a' : R' ⟶ S') (w : a ≫ κ = ψ ≫ a')
    (M : pbcModules T S') (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    ConcreteCategory.hom (((pbcRestrictSquare ψ κ a a' w).hom.app M).val.app V) x = x := by
  simp only [pbcRestrictSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    SheafOfModules.comp_val, PresheafOfModules.comp_app]
  erw [ConcreteCategory.comp_apply, restrictComp_apply, restrictComp_inv_apply]

private theorem pbcRestrict_map_apply {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) {M N : pbcModules T S} (p : M ⟶ N) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    ConcreteCategory.hom (((pbcRestrict a).map p).val.app V) x =
      ConcreteCategory.hom (p.val.app V) x :=
  rfl

private theorem pbcRestrictComp_inv_apply
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (M : pbcModules T B) (V : T.ProEtᵒᵖ) (x : M.val.obj V) :
    ConcreteCategory.hom (((pbcRestrictComp a b c h).inv.app M).val.app V) x = x :=
  restrictComp_inv_apply a b c h M V x

/-- Derived restriction squares paste along composites of coefficient maps. -/
theorem pbcDerivedRestrictSquare_comp
    {R S B R' S' B' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (ψ : R ⟶ R') (κS : S ⟶ S') (κB : B ⟶ B')
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (hc : a ≫ b = c)
    (a' : R' ⟶ S') (b' : S' ⟶ B') (c' : R' ⟶ B') (hc' : a' ≫ b' = c')
    (wa : a ≫ κS = ψ ≫ a') (wb : b ≫ κB = κS ≫ b') (wc : c ≫ κB = ψ ≫ c')
    (M : DerivedCategory (pbcModules T B')) :
    (pbcDerivedRestrict ψ).map ((pbcDerivedRestrictComp a' b' c' hc').hom.app M) ≫
        (pbcDerivedRestrictSquare ψ κB c c' wc).hom.app M =
      (pbcDerivedRestrictSquare ψ κS a a' wa).hom.app ((pbcDerivedRestrict b').obj M) ≫
        (pbcDerivedRestrict a).map ((pbcDerivedRestrictSquare κS κB b b' wb).hom.app M) ≫
        (pbcDerivedRestrictComp a b c hc).hom.app ((pbcDerivedRestrict κB).obj M) := by
  have ho (N : pbcModules T B') :
      (pbcRestrict ψ).map ((pbcRestrictComp a' b' c' hc').symm.hom.app N) ≫
          (pbcRestrictSquare ψ κS a a' wa).hom.app ((pbcRestrict b').obj N) ≫
          (pbcRestrict a).map ((pbcRestrictSquare κS κB b b' wb).hom.app N) =
        (pbcRestrictSquare ψ κB c c' wc).hom.app N ≫
          (pbcRestrictComp a b c hc).symm.hom.app ((pbcRestrict κB).obj N) := by
    ext V x
    simp only [Iso.symm_hom, SheafOfModules.comp_val, PresheafOfModules.comp_app,
      ConcreteCategory.comp_apply]
    erw [pbcRestrictComp_inv_apply a' b' c' hc' N V x,
      pbcRestrictSquare_hom_apply ψ κS a a' wa ((pbcRestrict b').obj N) V x,
      pbcRestrict_map_apply a ((pbcRestrictSquare κS κB b b' wb).hom.app N) V x,
      pbcRestrictSquare_hom_apply κS κB b b' wb N V x,
      pbcRestrictSquare_hom_apply ψ κB c c' wc N V x,
      pbcRestrictComp_inv_apply a b c hc ((pbcRestrict κB).obj N) V x]
  have hd := Functor.exactSquare_comp_forward
    (pbcRestrict b') (pbcRestrict a') (pbcRestrict c')
    (pbcRestrict b) (pbcRestrict a) (pbcRestrict c)
    (pbcRestrict κB) (pbcRestrict κS) (pbcRestrict ψ)
    (pbcRestrictSquare κS κB b b' wb) (pbcRestrictSquare ψ κS a a' wa)
    (pbcRestrictSquare ψ κB c c' wc)
    (pbcRestrictComp a' b' c' hc').symm (pbcRestrictComp a b c hc).symm ho M
  have hX (φ₁ : R' ⟶ S') (φ₂ : S' ⟶ B') (φ : R' ⟶ B') (hφ : φ₁ ≫ φ₂ = φ) :
      (Functor.mapDerivedCategoryNatIso (pbcRestrictComp φ₁ φ₂ φ hφ).symm ≪≫
        (Functor.mapDerivedCategoryCompIso (pbcRestrict φ₂) (pbcRestrict φ₁)).symm).hom =
          (pbcDerivedRestrictComp φ₁ φ₂ φ hφ).inv := by
    simp only [pbcDerivedRestrictComp, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.symm_hom]
    rfl
  have hY (φ₁ : R ⟶ S) (φ₂ : S ⟶ B) (φ : R ⟶ B) (hφ : φ₁ ≫ φ₂ = φ) :
      (Functor.mapDerivedCategoryNatIso (pbcRestrictComp φ₁ φ₂ φ hφ).symm ≪≫
        (Functor.mapDerivedCategoryCompIso (pbcRestrict φ₂) (pbcRestrict φ₁)).symm).hom =
          (pbcDerivedRestrictComp φ₁ φ₂ φ hφ).inv := by
    simp only [pbcDerivedRestrictComp, Functor.mapDerivedCategoryNatIso_symm,
      Iso.trans_hom, Iso.symm_hom]
    rfl
  rw [hX, hY] at hd
  have hh : (pbcDerivedRestrict ψ).map ((pbcDerivedRestrictComp a' b' c' hc').inv.app M) ≫
      (pbcDerivedRestrictSquare ψ κS a a' wa).hom.app ((pbcDerivedRestrict b').obj M) ≫
      (pbcDerivedRestrict a).map ((pbcDerivedRestrictSquare κS κB b b' wb).hom.app M) =
        (pbcDerivedRestrictSquare ψ κB c c' wc).hom.app M ≫
          (pbcDerivedRestrictComp a b c hc).inv.app ((pbcDerivedRestrict κB).obj M) := hd
  rw [← cancel_epi ((pbcDerivedRestrict ψ).map ((pbcDerivedRestrictComp a' b' c' hc').inv.app M)),
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% hh, Iso.inv_hom_id_app, Category.comp_id]

/-- Derived scalar extension commutes with relabelling along coefficient isomorphisms:
the mate of the derived restriction square. -/
def pbcRelabelExtend {R S R' S' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (ψ : R ≅ R') (κ : S ≅ S') (a : R ⟶ S) (a' : R' ⟶ S') (w : a ≫ κ.hom = ψ.hom ≫ a') :
    pbcDerivedRestrict ψ.hom ⋙ pbcDerivedExtend a ⟶
      pbcDerivedExtend a' ⋙ pbcDerivedRestrict κ.hom :=
  (mateEquiv (pbcDerivedScalarAdjunction a') (pbcDerivedScalarAdjunction a)).symm
    (pbcDerivedRestrictSquare ψ.hom κ.hom a a' w).hom

/-- The relabelling comparison of derived scalar extensions is invertible. -/
@[instance]
theorem pbcRelabelExtend_isIso {R S R' S' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (ψ : R ≅ R') (κ : S ≅ S') (a : R ⟶ S) (a' : R' ⟶ S') (w : a ≫ κ.hom = ψ.hom ≫ a') :
    IsIso (pbcRelabelExtend ψ κ a a' w) :=
  isIso_mateEquiv_symm_of_equivalence (pbcDerivedScalarAdjunction a')
    (pbcDerivedScalarAdjunction a) (pbcDerivedRestrictEquivalence ψ)
    (pbcDerivedRestrictEquivalence κ) (pbcDerivedRestrictSquare ψ.hom κ.hom a a' w)

/-- Relabelling along coefficient isomorphisms carries reduction transitions to
reduction transitions. -/
theorem pbcRelabelExtend_transition
    {R S B R' S' B' : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (ψ : R ≅ R') (κS : S ≅ S') (κB : B ≅ B')
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (hc : a ≫ b = c)
    (a' : R' ⟶ S') (b' : S' ⟶ B') (c' : R' ⟶ B') (hc' : a' ≫ b' = c')
    (wa : a ≫ κS.hom = ψ.hom ≫ a') (wb : b ≫ κB.hom = κS.hom ≫ b')
    (wc : c ≫ κB.hom = ψ.hom ≫ c') (Z : DerivedCategory (pbcModules T R')) :
    (pbcRelabelExtend ψ κS a a' wa).app Z ≫
        (pbcDerivedRestrict κS.hom).map (pbcReductionTransition a' b' c' hc' Z) ≫
        (pbcDerivedRestrictSquare κS.hom κB.hom b b' wb).hom.app ((pbcDerivedExtend c').obj Z) =
      pbcReductionTransition a b c hc ((pbcDerivedRestrict ψ.hom).obj Z) ≫
        (pbcDerivedRestrict b).map ((pbcRelabelExtend ψ κB c c' wc).app Z) :=
  homEquiv_symm_unit_mateEquiv_symm (pbcDerivedScalarAdjunction a')
    (pbcDerivedScalarAdjunction c') (pbcDerivedScalarAdjunction a)
    (pbcDerivedScalarAdjunction c) (pbcDerivedRestrictComp a' b' c' hc')
    (pbcDerivedRestrictComp a b c hc) (pbcDerivedRestrictSquare ψ.hom κS.hom a a' wa).hom
    (pbcDerivedRestrictSquare ψ.hom κB.hom c c' wc).hom
    (pbcDerivedRestrictSquare κS.hom κB.hom b b' wb).hom Z
    (pbcDerivedRestrictSquare_comp ψ.hom κS.hom κB.hom a b c hc a' b' c' hc' wa wb wc _)

end Relabel

/-- Reduction transitions are natural in the reduced object. -/
theorem pbcReductionTransition_naturality {T : Scheme.{u}}
    {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (hc : a ≫ b = c)
    {E F : DerivedCategory (pbcModules T R)} (q : E ⟶ F) :
    (pbcDerivedExtend a).map q ≫ pbcReductionTransition a b c hc F =
      pbcReductionTransition a b c hc E ≫
        (pbcDerivedRestrict b).map ((pbcDerivedExtend c).map q) := by
  unfold pbcReductionTransition
  rw [← Adjunction.homEquiv_naturality_left_symm,
    ← Adjunction.homEquiv_naturality_right_symm]
  congr 1
  rw [← Category.assoc, ← (pbcDerivedScalarAdjunction c).unit_naturality q]
  simp only [Category.assoc]
  congr 1
  exact (pbcDerivedRestrictComp a b c hc).inv.naturality ((pbcDerivedExtend c).map q)

section Iso

variable {X Y U : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
  {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A) (g : U ⟶ Y)

/-- The constant-ring comparisons of inverse images form a map of quotient systems. -/
private def constantCoefficientsSystem {Z W : Scheme.{u}} (m : W ⟶ Z) (I : Ideal A) :
    adicLisseRingSystem Z I ⋙ adicTowerInverseImage m ⟶ adicLisseRingSystem W I :=
  NatTrans.ofOpSequence (fun n ↦ (constantCoefficients m (A ⧸ I ^ (n + 1))).hom) (fun n ↦ by
    simp only [Functor.comp_map, adicLisseRingSystem, Functor.ofOpSequence_map_homOfLE_succ]
    exact constantCoefficients_naturality m (Ideal.Quotient.factorPowSucc I (n + 1)))

/-- The finite-level identification of an inverse-image quotient ring with a constant ring. -/
private def levelConstant {Z W : Scheme.{u}} (m : W ⟶ Z) (n : ℕ) :
    (adicTowerInverseImage m).obj ((pbcAdicRings Z d).obj (op n)) ≅
      (adicLisseRingSystem W d.ideal).obj (op n) :=
  ((adicTowerInverseImage m).mapIso (pbcLevelConstantComparison Z d n)).symm ≪≫
    constantCoefficients m (A ⧸ d.ideal ^ (n + 1))

/-- The identifications of inverse-image quotient rings with constant rings, as a map of
quotient systems. -/
private def levelConstantSystem {Z W : Scheme.{u}} (m : W ⟶ Z) :
    pbcAdicRings Z d ⋙ adicTowerInverseImage m ⟶ adicLisseRingSystem W d.ideal :=
  Functor.whiskerRight (pbcConstantSystemComparison Z d).inv (adicTowerInverseImage m) ≫
    constantCoefficientsSystem m d.ideal

private theorem levelConstant_hom {Z W : Scheme.{u}} (m : W ⟶ Z) (n : ℕ) :
    (levelConstant d m n).hom = (levelConstantSystem d m).app (op n) :=
  rfl

private theorem levelConstant_quotient {Z W : Scheme.{u}} (m : W ⟶ Z) (b a : ℕ)
    (hab : a ≤ b) :
    (adicTowerInverseImage m).map (pbcAdicQuotient Z d b a hab) ≫ (levelConstant d m a).hom =
      (levelConstant d m b).hom ≫ (adicLisseRingSystem W d.ideal).map (homOfLE hab).op := by
  rw [levelConstant_hom, levelConstant_hom]
  exact (levelConstantSystem d m).naturality (homOfLE hab).op

private theorem iso_trans_symm_comm {C : Type*} [Category C] {P₁ P₂ Q₁ Q₂ C₁ C₂ : C}
    (p : P₁ ⟶ P₂) (q : Q₁ ⟶ Q₂) (s : C₁ ⟶ C₂) (x₁ : P₁ ≅ C₁) (x₂ : P₂ ≅ C₂)
    (y₁ : Q₁ ≅ C₁) (y₂ : Q₂ ≅ C₂) (hx : p ≫ x₂.hom = x₁.hom ≫ s)
    (hy : q ≫ y₂.hom = y₁.hom ≫ s) :
    p ≫ (x₂ ≪≫ y₂.symm).hom = (x₁ ≪≫ y₁.symm).hom ≫ q := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% hx]
  congr 1
  rw [Iso.eq_inv_comp, ← reassoc_of% hy, Iso.hom_inv_id, Category.comp_id]

/-- The finite-level coefficient isomorphisms commute with the quotient maps. -/
private theorem pbcIsoLevelCoefficient_quotient (b a : ℕ) (hab : a ≤ b) :
    (adicTowerInverseImage (g ≫ inv f)).map (pbcAdicQuotient X d b a hab) ≫
        (pbcIsoLevelCoefficient f d g a).hom =
      (pbcIsoLevelCoefficient f d g b).hom ≫
        (adicTowerInverseImage g).map (pbcAdicQuotient Y d b a hab) := by
  have he (n : ℕ) : pbcIsoLevelCoefficient f d g n =
      levelConstant d (g ≫ inv f) n ≪≫ (levelConstant d g n).symm := by
    apply Iso.ext
    simp only [pbcIsoLevelCoefficient, levelConstant, Iso.trans_hom, Iso.symm_hom]
    erw [Iso.trans_inv]
    simp only [Category.assoc, Iso.symm_inv]
  rw [he, he]
  exact iso_trans_symm_comm _ _ _ _ _ _ _ (levelConstant_quotient d (g ≫ inv f) b a hab)
    (levelConstant_quotient d g b a hab)

/-- Restriction of an inverse image along coefficient maps depending on the scheme map
only changes along equal scheme maps. -/
private theorem pullback_restrict_congr {Z W : Scheme.{u}}
    (R : Sheaf (ProEt.topology Z) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology W) CommRingCat.{u + 1})
    (φ : ∀ m : W ⟶ Z, S ⟶ (adicTowerInverseImage m).obj R) {m m' : W ⟶ Z} (hm : m = m')
    (K : DerivedCategory (pbcModules Z R)) :
    Nonempty ((pbcDerivedRestrict (φ m)).obj ((adicTowerPullback m R).obj K) ≅
      (pbcDerivedRestrict (φ m')).obj ((adicTowerPullback m' R).obj K)) := by
  subst hm
  exact ⟨Iso.refl _⟩

/-- Inverse image along `g ≫ inv f` of ordinary pullback along `f` is the relabelled
inverse image along `g`. -/
theorem pbcIsoLocalPullback_nonempty (K : PbcCompletedDerived Y d) :
    Nonempty ((adicTowerPullback (g ≫ inv f) (pbcAdicCompletion X d)).obj
        ((completedOrdinaryPullback f d).obj K) ≅
      (pbcDerivedRestrict (pbcIsoLocalCoefficient f d g).hom).obj
        ((adicTowerPullback g (pbcAdicCompletion Y d)).obj K)) := by
  let h := g ≫ inv f
  let ι (m : U ⟶ Y) := d.integralRingIso m
  let chk := proEtaleRingCompositeCoefficients h f (d.completedRing Y) (d.completedRing X)
    ((adicTowerInverseImage h).obj (d.completedRing X)) (d.integralRingIso f) (Iso.refl _)
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, c, _⟩ :=
    proEtaleRingDerivedPullbackComposition h f (d.completedRing Y) (d.completedRing X)
      ((adicTowerInverseImage h).obj (d.completedRing X)) (d.integralRingIso f) (Iso.refl _)
      chk rfl
  have hchk : chk.inv = (d.integralRingIso h).hom ≫ (ι (h ≫ f)).inv := by
    rw [Iso.eq_comp_inv, ← cancel_epi chk.hom, Iso.hom_inv_id_assoc]
    have hc := congrArg Iso.hom (fourCornersIntegral_comp d h f)
    simp only [chk, ι, hc, proEtaleRingCompositeCoefficients, Iso.trans_hom, Iso.refl_hom,
      Category.id_comp, Category.assoc]
  have hψ : (pbcIsoLocalCoefficient f d g).hom = (d.integralRingIso h).hom ≫ (ι g).inv := by
    erw [Iso.eq_comp_inv]
    have hc := congrArg Iso.hom (fourCornersIntegral_comp d g (inv f))
    erw [hc]
    simp only [ι, proEtaleRingCompositeCoefficients, pbcIsoLocalCoefficient, Iso.trans_hom,
      Functor.mapIso_hom, Iso.app_hom, Category.assoc]
    rfl
  let ρ := proEtaleRingRestrictionDerivedPullback (h ≫ f) (d.completedRing Y)
    (d.completedRing Y) ((adicTowerInverseImage h).obj (d.completedRing X))
    ((adicTowerInverseImage (h ≫ f)).obj (d.completedRing Y)) (𝟙 _) chk.inv chk (Iso.refl _)
    (by simp)
  let rid := Functor.mapDerivedCategoryNatIso (pbcRestrictId (d.completedRing Y)) ≪≫
    Functor.mapDerivedCategoryIdIso _
  obtain ⟨e⟩ := pullback_restrict_congr (d.completedRing Y)
    ((adicTowerInverseImage h).obj (d.completedRing X))
    (fun m ↦ (d.integralRingIso h).hom ≫ (ι m).inv) (m := h ≫ f) (m' := g) (by simp [h]) K
  rw [hψ]
  refine ⟨(adicTowerPullback h (pbcAdicCompletion X d)).mapIso
      ((pullbackDatumOrdinaryTransport f d).app K) ≪≫ (c.app K).symm ≪≫
    (proEtaleRingDerivedPullback (h ≫ f) (d.completedRing Y)
      ((adicTowerInverseImage h).obj (d.completedRing X)) chk).mapIso (rid.app K).symm ≪≫
    (ρ.app K).symm ≪≫ ?_⟩
  beta_reduce at e
  rw [← hchk] at e
  exact e

end Iso

end AlgebraicGeometry.Scheme
