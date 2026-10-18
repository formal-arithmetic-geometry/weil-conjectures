/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NU and S1
-/
module

public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimit
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitAcyclic
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.CategoryTheory.SmallModuleDiagramsGrothendieck
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective

/-!
# Derived direct image and strict tower limits

Source: Stacks Project, Cohomology on Sites, Tags 0A07 and 0940
(blueprint: lem-weil-ringed-tower-pushforward-limit-comparison).
-/

@[expose] public section

universe u w uA uB vA vB

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

section Helpers

variable {A : Type uA} {B : Type uB} [Category.{vA} A] [Category.{vB} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]

private theorem towerComparison_existsComposite
    {T : Type u} [Category T] [Abelian T] [HasDerivedCategory.{w} T]
    [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : B ⥤ T) [F.Additive] [G.Additive]
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (RG : DerivedCategory.{w} B ⥤ DerivedCategory.{w} T)
    (ηf : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (ηg : G.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RG)
    (hf : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (ηf.app I))
    (hg : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (ηg.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) :
    ∃ (η : (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ (RF ⋙ RG)),
      (RF ⋙ RG).IsRightDerivedFunctor η
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ)) ∧
      ∀ X, η.app X = ηg.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫
        RG.map (ηf.app X) := by
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let Gc := G.mapHomologicalComplex (ComplexShape.up ℤ)
  let η : (F ⋙ G).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ (RF ⋙ RG) :=
    { app := fun X ↦ ηg.app (Fc.obj X) ≫ RG.map (ηf.app X)
      naturality := by
        intro X Y a
        change DerivedCategory.Q.map (Gc.map (Fc.map a)) ≫
            (ηg.app (Fc.obj Y) ≫ RG.map (ηf.app Y)) =
          (ηg.app (Fc.obj X) ≫ RG.map (ηf.app X)) ≫ RG.map (RF.map (DerivedCategory.Q.map a))
        have hn := ηg.naturality (Fc.map a)
        have hm := ηf.naturality a
        dsimp only [Functor.comp_map] at hn hm
        rw [← Category.assoc, hn]
        simp only [Category.assoc]
        rw [← RG.map_comp, hm, RG.map_comp] }
  refine ⟨η, ?_, fun _ ↦ rfl⟩
  apply (derives (F ⋙ G)).isRightDerivedFunctor_of_isIso η
  intro X
  have := hf X.obj X.property
  have := hg X.obj X.property
  change IsIso (ηg.app (Fc.obj X.obj) ≫ RG.map (ηf.app X.obj))
  infer_instance

variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)]

private theorem towerComparison_existsEvaluation :
    ∃ (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A)),
      Nonempty (DerivedCategory.Q.{w} ⋙ E ≅
        HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
          (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
            (DerivedCategory.{w} A)).obj DerivedCategory.Q.{w}) := by
  let H : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A) :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
        (DerivedCategory.{w} A)).obj DerivedCategory.Q.{w}
  have h : (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)).IsInvertedBy H := by
    intro X Y f hf
    have : QuasiIso f := hf
    have : ∀ n, IsIso ((H.map f).app n) := by
      intro n
      change IsIso (DerivedCategory.Q.map
        ((((evaluation ℕᵒᵖ A).obj n).mapHomologicalComplex (ComplexShape.up ℤ)).map f))
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact ⟨Localization.lift H h DerivedCategory.Q, ⟨Localization.fac H h DerivedCategory.Q⟩⟩

variable [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

private theorem towerComparison_existsEvaluationIso
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (RT : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ B))
    (ηf : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (ηt : ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RT)
    (hIf : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (ηf.app I))
    (hIt : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective → IsIso (ηt.app I))
    (EA : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (EB : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} B))
    (εA : DerivedCategory.Q.{w} ⋙ EA ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
          (DerivedCategory.{w} A)).obj DerivedCategory.Q.{w})
    (εB : DerivedCategory.Q.{w} ⋙ EB ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ (CochainComplex B ℤ)
          (DerivedCategory.{w} B)).obj DerivedCategory.Q.{w}) :
    ∃ e : RT ⋙ EB ≅ EA ⋙
        (Functor.whiskeringRight ℕᵒᵖ (DerivedCategory.{w} A) (DerivedCategory.{w} B)).obj RF,
      ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ),
        (EB.map (ηt.app I)).app n ≫ (e.hom.app (DerivedCategory.Q.{w}.obj I)).app n ≫
            RF.map ((εA.hom.app I).app n) =
          (εB.hom.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)).app n ≫ ηf.app (I.asFunctor.obj n) := by
  let Fc := ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let WR := (Functor.whiskeringRight ℕᵒᵖ (DerivedCategory.{w} A)
    (DerivedCategory.{w} B)).obj RF
  let HA : CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A) :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
        (DerivedCategory.{w} A)).obj DerivedCategory.Q.{w}
  let HB : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} B) :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (Functor.whiskeringRight ℕᵒᵖ (CochainComplex B ℤ)
        (DerivedCategory.{w} B)).obj DerivedCategory.Q.{w}
  let τ : Fc ⋙ HB ⟶ HA ⋙ WR :=
    { app := fun X ↦
        { app := fun n ↦ ηf.app (X.asFunctor.obj n)
          naturality := fun n m g ↦ ηf.naturality (X.asFunctor.map g) }
      naturality := by
        intro X Y g
        ext n
        exact ηf.naturality
          ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map g).app n) }
  let H := Fc ⋙ DerivedCategory.Q.{w} ⋙ EB
  have hd : (CochainComplex.KInjectives.localizerMorphism (ℕᵒᵖ ⥤ A)).Derives H := by
    intro X Y g hg
    have hi : IsIso (DerivedCategory.Q.map (Fc.map g.hom)) :=
      derives ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) g hg
    exact EB.map_isIso (DerivedCategory.Q.map (Fc.map g.hom))
  let α : H ⟶ DerivedCategory.Q.{w} ⋙ (RT ⋙ EB) :=
    Functor.whiskerRight ηt EB
  let β : H ⟶ DerivedCategory.Q.{w} ⋙ (EA ⋙ WR) :=
    Functor.whiskerLeft Fc εB.hom ≫ τ ≫ Functor.whiskerRight εA.inv WR
  have hα : (RT ⋙ EB).IsRightDerivedFunctor α
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) := by
    apply hd.isRightDerivedFunctor_of_isIso α
    intro X
    have := hIt X.obj X.property
    change IsIso (EB.map (ηt.app X.obj))
    infer_instance
  have hβ : (EA ⋙ WR).IsRightDerivedFunctor β
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) := by
    apply hd.isRightDerivedFunctor_of_isIso β
    intro X
    have hτ : IsIso (τ.app X.obj) := by
      have : ∀ n, IsIso ((τ.app X.obj).app n) := by
        intro n
        have : X.obj.IsKInjective := X.property
        exact hIf _ (tower_evaluation_isKInjective A X.obj n)
      exact NatIso.isIso_of_isIso_app _
    dsimp [β]
    infer_instance
  let e := Functor.rightDerivedUnique (RT ⋙ EB) (EA ⋙ WR) α β
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ))
  refine ⟨e, ?_⟩
  intro I n
  have he := Functor.rightDerivedNatTrans_app (RT ⋙ EB) (EA ⋙ WR) α β
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) (𝟙 H) I
  have he' := congrArg (fun k ↦ k.app n) he
  change (EB.map (ηt.app I)).app n ≫ (e.hom.app (DerivedCategory.Q.obj I)).app n =
    𝟙 _ ≫ (β.app I).app n at he'
  rw [← Category.assoc, he']
  dsimp [β, τ, WR]
  have hc : (εA.inv.app I).app n ≫ (εA.hom.app I).app n = 𝟙 _ :=
    congrArg (fun k ↦ k.app n) (εA.inv_hom_id_app I)
  simp only [Category.id_comp, Category.assoc, ← RF.map_comp, hc]
  erw [RF.map_id]
  erw [Category.comp_id]

variable [HasLimitsOfShape ℕᵒᵖ A]

private theorem towerComparison_existsProjections
    (L : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (η : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ L)
    [L.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ))]
    (E : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ (ℕᵒᵖ ⥤ DerivedCategory.{w} A))
    (ε : DerivedCategory.Q.{w} ⋙ E ≅
      HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
        (Functor.whiskeringRight ℕᵒᵖ (CochainComplex A ℤ)
          (DerivedCategory.{w} A)).obj DerivedCategory.Q.{w}) :
    ∃ (p : ∀ n, L ⟶ E ⋙ (evaluation ℕᵒᵖ (DerivedCategory.{w} A)).obj n),
      ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ),
        η.app X ≫ (p n).app (DerivedCategory.Q.{w}.obj X) ≫ (ε.hom.app X).app n =
          DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex
            (lim.π n : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⟶ (evaluation ℕᵒᵖ A).obj n)
              (ComplexShape.up ℤ)).app X) := by
  let W := HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)
  let β (n : ℕᵒᵖ) :
      (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ (E ⋙ (evaluation ℕᵒᵖ (DerivedCategory.{w} A)).obj n) :=
    Functor.whiskerRight
      (NatTrans.mapHomologicalComplex (lim.π n) (ComplexShape.up ℤ)) DerivedCategory.Q ≫
      Functor.whiskerRight ε.inv ((evaluation ℕᵒᵖ (DerivedCategory.{w} A)).obj n)
  let p (n : ℕᵒᵖ) := L.rightDerivedDesc η W
    (E ⋙ (evaluation ℕᵒᵖ (DerivedCategory.{w} A)).obj n) (β n)
  refine ⟨p, ?_⟩
  intro X n
  rw [← Category.assoc, Functor.rightDerived_fac_app]
  dsimp [β]
  simp only [Category.assoc, ← NatTrans.comp_app, ε.inv_hom_id,
    NatTrans.id_app]
  exact Category.comp_id _

omit [HasDerivedCategory A] [HasDerivedCategory (ℕᵒᵖ ⥤ A)] in
private theorem towerComparison_limPreservesKInjective
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).PreservesKInjectiveComplexes := by
  exact Adjunction.preservesKInjectiveComplexes
    (constLimAdj : (Functor.const ℕᵒᵖ : A ⥤ (ℕᵒᵖ ⥤ A)) ⊣ lim)

private theorem towerComparison_existsLimitIso
    [HasLimitsOfShape ℕᵒᵖ B]
    [Abelian.HasKInjectiveResolutions (ℕᵒᵖ ⥤ A)]
    [(lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive] [(lim : (ℕᵒᵖ ⥤ B) ⥤ B).Additive]
    (F : A ⥤ B) [F.Additive]
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (RT : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} (ℕᵒᵖ ⥤ B))
    (LA : DerivedCategory.{w} (ℕᵒᵖ ⥤ A) ⥤ DerivedCategory.{w} A)
    (LB : DerivedCategory.{w} (ℕᵒᵖ ⥤ B) ⥤ DerivedCategory.{w} B)
    (ηf : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (ηt : ((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RT)
    (ηA : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ LA)
    (ηB : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
      DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ LB)
    (hf : ∀ I : CochainComplex A ℤ, I.IsKInjective → IsIso (ηf.app I))
    (ht : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective → IsIso (ηt.app I))
    (hA : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective → IsIso (ηA.app I))
    (hB : ∀ I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ, I.IsKInjective →
      IsIso (ηB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I)))
    (c : (lim : (ℕᵒᵖ ⥤ A) ⥤ A) ⋙ F ≅
      (Functor.whiskeringRight ℕᵒᵖ A B).obj F ⋙ (lim : (ℕᵒᵖ ⥤ B) ⥤ B)) :
    ∃ a : LA ⋙ RF ≅ RT ⋙ LB,
      ∀ X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ,
        ηf.app (((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) ≫ RF.map (ηA.app X) ≫
          a.hom.app (DerivedCategory.Q.{w}.obj X) =
        DerivedCategory.Q.{w}.map
            ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app X) ≫
          ηB.app ((((Functor.whiskeringRight ℕᵒᵖ A B).obj F).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj X) ≫ LB.map (ηt.app X) := by
  have := towerComparison_limPreservesKInjective (A := A)
  obtain ⟨α, hα, hαapp⟩ := towerComparison_existsComposite
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A) F LA RF ηA ηf hA (fun I hI ↦ by
      have := hI
      exact hf _ inferInstance)
  obtain ⟨β, hβ, hβapp⟩ := towerComparison_existsComposite
    ((Functor.whiskeringRight ℕᵒᵖ A B).obj F) (lim : (ℕᵒᵖ ⥤ B) ⥤ B)
    RT LB ηt ηB ht hB
  have := hα
  have := hβ
  let τ := Functor.isoWhiskerRight (NatIso.mapHomologicalComplex c (ComplexShape.up ℤ))
    DerivedCategory.Q.{w}
  let a := Functor.rightDerivedNatIso (LA ⋙ RF) (RT ⋙ LB) α β
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) τ
  refine ⟨a, ?_⟩
  intro X
  have h := Functor.rightDerivedNatTrans_app (LA ⋙ RF) (RT ⋙ LB) α β
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (ComplexShape.up ℤ)) τ.hom X
  rw [hαapp, hβapp] at h
  rw [← Category.assoc]
  exact h

end Helpers

private theorem towerComparison_underlyingPreservesLimits
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) :
    PreservesLimitsOfShape ℕᵒᵖ
      (SheafOfModules.toSheaf.{u} R ⋙ sheafCompose J (forget AddCommGrpCat.{u})) := by
  let U := SheafOfModules.toSheaf.{u} R ⋙ sheafCompose J (forget AddCommGrpCat.{u})
  have : PreservesLimitsOfShape ℕᵒᵖ (U ⋙ sheafToPresheaf J (Type u)) := by
    change PreservesLimitsOfShape ℕᵒᵖ
      (SheafOfModules.forget R ⋙ PresheafOfModules.toPresheaf R.obj ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat (Type u)).obj (forget AddCommGrpCat))
    infer_instance
  exact preservesLimitsOfShape_of_reflects_of_preserves U (sheafToPresheaf J (Type u))
    (J := ℕᵒᵖ)

private theorem towerComparison_modulesPreservesLimits
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{u}} {S : Sheaf K RingCat.{u}}
    (f : RingedToposMorphism R S) : PreservesLimitsOfShape ℕᵒᵖ f.modules := by
  let UR := SheafOfModules.toSheaf.{u} R ⋙ sheafCompose J (forget AddCommGrpCat.{u})
  let US := SheafOfModules.toSheaf.{u} S ⋙ sheafCompose K (forget AddCommGrpCat.{u})
  have : PreservesLimitsOfShape ℕᵒᵖ UR := towerComparison_underlyingPreservesLimits R
  have : PreservesLimitsOfShape ℕᵒᵖ US := towerComparison_underlyingPreservesLimits S
  have : ReflectsLimitsOfShape ℕᵒᵖ US := reflectsLimitsOfShape_of_reflectsIsomorphisms
  have : PreservesLimitsOfSize.{0, 0} f.direct := f.adj.rightAdjoint_preservesLimits
  have : PreservesLimitsOfShape ℕᵒᵖ (f.modules ⋙ US) :=
    preservesLimitsOfShape_of_natIso f.underlying.symm
  exact preservesLimitsOfShape_of_reflects_of_preserves f.modules US

set_option maxHeartbeats 1200000 in
-- Repeated tower localizations and composite-unit equations require extra elaboration steps.
/-- The canonical comparison of derived direct image with strict tower inverse limit.

Source: Stacks Project, Cohomology on Sites, Tags 0A07, 0940 and 0941
(blueprint: lem-weil-ringed-tower-pushforward-limit-comparison).

`ℕ` indexes the positive levels by `n + 1`. The functors and their units are total
right derived functors with K-injective normalization. `E_R`, `E_S` evaluate derived
strict towers, including transitions; `εR`, `εS` identify them with evaluation on
complexes. The underived comparison `c` is characterized by `limit.post`, hence is
exactly the common-direct-image identification. The unit equation for `a` gives its
common-direct-image normalization, and the final equation is compatibility with every
projection. The equation for `e` fixes the evaluation identifications on K-injectives.

Proof:
1. Construct total right derived functors using K-injective resolutions. Tower
   resolutions exist because the strict diagram category is Grothendieck abelian.
2. Localize strict evaluation into towers of derived objects. Exact evaluation
   preserves K-injectives, so uniqueness of right derived functors gives `e`,
   including its normalization on all complexes. Define the projections by the
   right derived functor universal property.
3. The underlying sheaf direct image preserves limits; the forgetful module functors
   preserve and reflect limits. This constructs `c` as `limit.post`. The exact
   constant-tower left adjoint shows that inverse limit preserves K-injectives.
4. The K-flat adjunction argument in `ringedTowerPushforwardLimitAcyclic` shows that
   a K-injective resolution of the levelwise pushforward remains a quasi-isomorphism
   after inverse limit. Hence both composite units compute the total right derived
   functor of the common underived composite. Its universal property gives `a`
   with the displayed normalization.
5. Apply uniqueness of right derived transformations to the two proposed projection
   maps. Before localization their equality follows from the normalization of `a`,
   naturality of the target projection, normalization of `e`, the source and target
   projection equations, and the strict identity `c` followed by a limit projection
   equals pushforward of that projection. -/
theorem ringedTowerPushforwardLimitComparison
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J RingCat.{u}) (S : Sheaf K RingCat.{u})
    (_hcommR : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    (_hcommS : ∀ (U : Dᵒᵖ) (a b : S.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S)]
    [HasDerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R))]
    [HasDerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S))]
    (f : RingedToposMorphism R S) :
    ∃ (Rf : DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R) ⥤ DerivedCategory.{w}
      (ringedSiteModules.{u, u, u, u} S))
      (Rt : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ⥤ DerivedCategory.{w}
        ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)))
      (LR : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ⥤ DerivedCategory.{w}
        (ringedSiteModules.{u, u, u, u} R))
      (LS : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)) ⥤ DerivedCategory.{w}
        (ringedSiteModules.{u, u, u, u} S))
      (ηf : (f.modules).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ Rf)
      (ηt : (((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R) (ringedSiteModules.{u,
        u, u, u} S)).obj f.modules)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ Rt)
      (ηR : ((lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R) ⥤ ringedSiteModules.{u, u, u, u}
        R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ LR)
      (ηS : ((lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S) ⥤ ringedSiteModules.{u, u, u, u}
        S)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
        DerivedCategory.Q.{w} ⋙ LS),
      Rf.IsRightDerivedFunctor ηf
        (HomologicalComplex.quasiIso (ringedSiteModules.{u, u, u, u} R) (ComplexShape.up ℤ)) ∧
      (∀ (I : CochainComplex (ringedSiteModules.{u, u, u, u} R) ℤ), I.IsKInjective → IsIso (ηf.app
        I)) ∧
      Rt.IsRightDerivedFunctor ηt
        (HomologicalComplex.quasiIso ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) (ComplexShape.up ℤ))
          ∧
      (∀ (I : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ℤ), I.IsKInjective → IsIso
        (ηt.app I)) ∧
      LR.IsRightDerivedFunctor ηR
        (HomologicalComplex.quasiIso ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) (ComplexShape.up ℤ))
          ∧
      (∀ (I : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ℤ), I.IsKInjective → IsIso
        (ηR.app I)) ∧
      LS.IsRightDerivedFunctor ηS
        (HomologicalComplex.quasiIso ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)) (ComplexShape.up ℤ))
          ∧
      (∀ (I : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)) ℤ), I.IsKInjective → IsIso
        (ηS.app I)) ∧
      ∃ (E_R : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ⥤ (ℕᵒᵖ ⥤
        DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R)))
        (E_S : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)) ⥤ (ℕᵒᵖ ⥤
          DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S)))
        (εR : DerivedCategory.Q.{w} ⋙ E_R ≅ HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
          (Functor.whiskeringRight ℕᵒᵖ (CochainComplex (ringedSiteModules.{u, u, u, u} R) ℤ)
          (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R))).obj DerivedCategory.Q.{w})
        (εS : DerivedCategory.Q.{w} ⋙ E_S ≅ HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
          (Functor.whiskeringRight ℕᵒᵖ (CochainComplex (ringedSiteModules.{u, u, u, u} S) ℤ)
          (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S))).obj DerivedCategory.Q.{w})
        (pR : ∀ n : ℕᵒᵖ, LR ⟶ E_R ⋙ (evaluation ℕᵒᵖ (DerivedCategory.{w} (ringedSiteModules.{u, u,
          u, u} R))).obj n)
        (pS : ∀ n : ℕᵒᵖ, LS ⟶ E_S ⋙ (evaluation ℕᵒᵖ (DerivedCategory.{w} (ringedSiteModules.{u, u,
          u, u} S))).obj n)
        (c : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R) ⥤ ringedSiteModules.{u, u, u, u} R) ⋙
          f.modules ≅ ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R)
          (ringedSiteModules.{u, u, u, u} S)).obj f.modules) ⋙ (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u,
          u, u, u} S) ⥤ ringedSiteModules.{u, u, u, u} S))
        (e : Rt ⋙ E_S ≅ E_R ⋙
          (Functor.whiskeringRight ℕᵒᵖ (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} R))
            (DerivedCategory.{w} (ringedSiteModules.{u, u, u, u} S))).obj Rf)
        (a : LR ⋙ Rf ≅ Rt ⋙ LS),
        (∀ H : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R), c.hom.app H = limit.post H f.modules) ∧
        (∀ (X : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ℤ) (n : ℕᵒᵖ),
          ηR.app X ≫ (pR n).app (DerivedCategory.Q.{w}.obj X) ≫ (εR.hom.app X).app n =
            DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex
              (lim.π n : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R) ⥤ ringedSiteModules.{u, u,
                u, u} R) ⟶ (evaluation ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R)).obj n)
                (ComplexShape.up ℤ)).app X)) ∧
        (∀ (X : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S)) ℤ) (n : ℕᵒᵖ),
          ηS.app X ≫ (pS n).app (DerivedCategory.Q.{w}.obj X) ≫ (εS.hom.app X).app n =
            DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex
              (lim.π n : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S) ⥤ ringedSiteModules.{u, u,
                u, u} S) ⟶ (evaluation ℕᵒᵖ (ringedSiteModules.{u, u, u, u} S)).obj n)
                (ComplexShape.up ℤ)).app X)) ∧
        (∀ (I : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ℤ), I.IsKInjective → ∀ n :
          ℕᵒᵖ,
          (E_S.map (ηt.app I)).app n ≫ (e.hom.app (DerivedCategory.Q.{w}.obj I)).app n ≫
              Rf.map ((εR.hom.app I).app n) =
            (εS.hom.app (((((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R)
              (ringedSiteModules.{u, u, u, u} S)).obj f.modules)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)).app n ≫ ηf.app (I.asFunctor.obj n)) ∧
        (∀ X : CochainComplex ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R)) ℤ,
          ηf.app ((((lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R) ⥤ ringedSiteModules.{u, u, u, u}
            R)).mapHomologicalComplex (ComplexShape.up ℤ)).obj X) ≫ Rf.map (ηR.app X) ≫
              a.hom.app (DerivedCategory.Q.{w}.obj X) =
            DerivedCategory.Q.{w}.map ((NatTrans.mapHomologicalComplex c.hom (ComplexShape.up
              ℤ)).app X) ≫
              ηS.app (((((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R)
                (ringedSiteModules.{u, u, u, u} S)).obj f.modules)).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj X) ≫ LS.map (ηt.app X)) ∧
        (∀ (M : DerivedCategory.{w} ((ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R))) (n : ℕᵒᵖ),
          a.hom.app M ≫ (pS n).app (Rt.obj M) ≫ (e.hom.app M).app n =
            Rf.map ((pR n).app M)) := by
  let : Abelian (ringedSiteModules.{u} R) := inferInstance
  let : Abelian (ringedSiteModules.{u} S) := inferInstance
  let : Abelian (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) := inferInstance
  let : Abelian (ℕᵒᵖ ⥤ ringedSiteModules.{u} S) := inferInstance
  let : f.modules.PreservesZeroMorphisms := inferInstance
  have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u, u, u, u} R) :=
    SheafOfModules.isGrothendieckAbelian R
  have : IsGrothendieckAbelian.{u} (ringedSiteModules.{u, u, u, u} S) :=
    SheafOfModules.isGrothendieckAbelian S
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R) :=
    by
      have := smallModuleDiagrams_isGrothendieckAbelian J R
        (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
      exact IsGrothendieckAbelian.of_equivalence
        (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  have : IsGrothendieckAbelian.{u} (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S) :=
    by
      have := smallModuleDiagrams_isGrothendieckAbelian K S
        (ULiftHom.{u} (ULift.{u} ℕᵒᵖ))
      exact IsGrothendieckAbelian.of_equivalence
        (ULiftHomULiftCategory.equiv.{u, u} ℕᵒᵖ).congrLeft.symm
  obtain ⟨Rf, ηf, hf, hIf⟩ := exists_derived f.modules
  obtain ⟨Rt, ηt, ht, hIt⟩ := exists_derived
    ((Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u, u, u, u} R)
      (ringedSiteModules.{u, u, u, u} S)).obj f.modules)
  have : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ⥤ _).Additive :=
    Functor.additive_of_preserves_binary_products _
  have : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u} S) ⥤ _).Additive :=
    Functor.additive_of_preserves_binary_products _
  obtain ⟨LR, ηR, hR, hIR⟩ := exists_derived
    (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} R) ⥤ _)
  obtain ⟨LS, ηS, hS, hIS⟩ := exists_derived
    (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u, u, u, u} S) ⥤ _)
  have := hf
  have := ht
  have := hR
  have := hS
  obtain ⟨ER, ⟨εR⟩⟩ := towerComparison_existsEvaluation (A := ringedSiteModules.{u} R)
  obtain ⟨ES, ⟨εS⟩⟩ := towerComparison_existsEvaluation (A := ringedSiteModules.{u} S)
  obtain ⟨pR, hpR⟩ := towerComparison_existsProjections LR ηR ER εR
  obtain ⟨pS, hpS⟩ := towerComparison_existsProjections LS ηS ES εS
  obtain ⟨e, he⟩ := towerComparison_existsEvaluationIso f.modules Rf Rt ηf ηt
    hIf hIt ER ES εR εS
  have := towerComparison_modulesPreservesLimits f
  let c := preservesLimitNatIso f.modules (J := ℕᵒᵖ)
  let Ft := (Functor.whiskeringRight ℕᵒᵖ (ringedSiteModules.{u} R)
    (ringedSiteModules.{u} S)).obj f.modules
  let Ftc := Ft.mapHomologicalComplex (ComplexShape.up ℤ)
  let LSc := (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u} S) ⥤ _).mapHomologicalComplex
    (ComplexShape.up ℤ)
  have hacyc (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ℤ)
      (hI : I.IsKInjective) (T : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} S) ℤ)
      (hT : T.IsKInjective) (j : Ftc.obj I ⟶ T) [QuasiIso j] :
      QuasiIso (LSc.map j) := by
    exact ringedTowerPushforwardLimitAcyclic R S _hcommR _hcommS f I hI T hT j
  have hBS (I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ℤ)
      (hI : I.IsKInjective) : IsIso (ηS.app (Ftc.obj I)) := by
    obtain ⟨T, hT, j, _, hj⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
      (Ftc.obj I)
    have : QuasiIso j := hj
    have : QuasiIso (LSc.map j) := hacyc I hI T hT j
    have : IsIso (ηS.app T) := hIS T hT
    have hn := ηS.naturality j
    dsimp only [Functor.comp_map] at hn
    have : IsIso (ηS.app (Ftc.obj I) ≫ LS.map (DerivedCategory.Q.map j)) := by
      rw [← hn]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (LS.map (DerivedCategory.Q.map j))
  obtain ⟨a, ha⟩ := towerComparison_existsLimitIso f.modules Rf Rt LR LS
    ηf ηt ηR ηS hIf hIt hIR hBS c
  refine ⟨Rf, Rt, LR, LS, ηf, ηt, ηR, ηS, hf, hIf, ht, hIt, hR, hIR, hS, hIS,
    ER, ES, εR, εS, pR, pS, c, e, a, ?_, hpR, hpS, (fun I _ n ↦ he I n), ha, ?_⟩
  · intro H
    rfl
  · intro M n
    have := towerComparison_limPreservesKInjective
      (A := ringedSiteModules.{u} R)
    obtain ⟨α, hα, hαapp⟩ := towerComparison_existsComposite
      (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ⥤ _) f.modules
      LR Rf ηR ηf hIR (fun I hI ↦ by
        have := hI
        exact hIf _ inferInstance)
    have := hα
    let γ₁ : LR ⋙ Rf ⟶ ER ⋙
        (evaluation ℕᵒᵖ (DerivedCategory.{w} (ringedSiteModules.{u} R))).obj n ⋙ Rf :=
      a.hom ≫ Functor.whiskerLeft Rt (pS n) ≫
        Functor.whiskerRight e.hom
          ((evaluation ℕᵒᵖ (DerivedCategory.{w} (ringedSiteModules.{u} S))).obj n)
    let γ₂ : LR ⋙ Rf ⟶ ER ⋙
        (evaluation ℕᵒᵖ (DerivedCategory.{w} (ringedSiteModules.{u} R))).obj n ⋙ Rf :=
      Functor.whiskerRight (pR n) Rf
    have hγ : γ₁ = γ₂ := by
      apply Functor.rightDerived_ext (LR ⋙ Rf) α
        (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) (ComplexShape.up ℤ))
      apply NatTrans.ext
      funext X
      change α.app X ≫ (a.hom.app (DerivedCategory.Q.obj X) ≫
          (pS n).app (Rt.obj (DerivedCategory.Q.obj X)) ≫
          (e.hom.app (DerivedCategory.Q.obj X)).app n) =
        α.app X ≫ Rf.map ((pR n).app (DerivedCategory.Q.obj X))
      rw [hαapp]
      apply (cancel_mono (Rf.map ((εR.hom.app X).app n))).mp
      have hn := (pS n).naturality (ηt.app X)
      dsimp only [Functor.comp_map] at hn
      have hchain :
          (NatTrans.mapHomologicalComplex c.hom (ComplexShape.up ℤ)).app X ≫
            (NatTrans.mapHomologicalComplex
              (lim.π n : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u} S) ⥤ _) ⟶
                (evaluation ℕᵒᵖ (ringedSiteModules.{u} S)).obj n)
              (ComplexShape.up ℤ)).app (Ftc.obj X) =
          (f.modules.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex
              (lim.π n : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ⥤ _) ⟶
                (evaluation ℕᵒᵖ (ringedSiteModules.{u} R)).obj n)
              (ComplexShape.up ℤ)).app X) := by
        apply HomologicalComplex.hom_ext
        intro i
        exact preservesLimitIso_hom_π f.modules (X.X i) n
      have hfπ := ηf.naturality
        ((NatTrans.mapHomologicalComplex
          (lim.π n : (lim : (ℕᵒᵖ ⥤ ringedSiteModules.{u} R) ⥤ _) ⟶
            (evaluation ℕᵒᵖ (ringedSiteModules.{u} R)).obj n)
          (ComplexShape.up ℤ)).app X)
      dsimp only [Functor.comp_map] at hfπ
      simp only [Category.assoc]
      have ha' := congrArg (fun k ↦ k ≫
        (pS n).app (Rt.obj (DerivedCategory.Q.obj X)) ≫
        (e.hom.app (DerivedCategory.Q.obj X)).app n ≫
        Rf.map ((εR.hom.app X).app n)) (ha X)
      simp only [Category.assoc] at ha'
      rw [ha']
      erw [← Category.assoc (LS.map (ηt.app X)), hn]
      simp only [Category.assoc]
      erw [he X n]
      have hs' := congrArg (fun k ↦ k ≫ ηf.app (X.asFunctor.obj n))
        (hpS (Ftc.obj X) n)
      simp only [Category.assoc] at hs'
      erw [hs']
      erw [← Category.assoc, ← DerivedCategory.Q.map_comp, hchain, hfπ]
      simp only [← Rf.map_comp]
      erw [hpR X n]
    exact NatTrans.congr_app hγ M

end CategoryTheory
