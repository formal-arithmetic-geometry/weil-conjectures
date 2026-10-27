/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import Sheaf.CategoryTheory.AlgebraDiagramEvaluationAdjunctionNormalizationDefs
import all Sheaf.CategoryTheory.DiagramRingRestrictionPushforward
import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory

section
variable {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B]
    [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive]

private def diagramUnit : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
    DerivedCategory.Q.{w} ⋙ F.rightDerivedFunctor where
  app := F.rightDerivedFunctorUnitQ
  naturality _ _ f := F.rightDerivedFunctorUnitQ_naturality f

private theorem diagramUnit_isIso (I : CochainComplex A ℤ) (hI : I.IsKInjective) :
    IsIso ((diagramUnit F).app I) := by
  let := hI
  change IsIso (F.rightDerivedFunctorUnitQ I)
  rw [F.rightDerivedFunctorUnitQ_eq]
  infer_instance

private theorem diagramUnit_isDerived : F.rightDerivedFunctor.IsRightDerivedFunctor
    (diagramUnit F) (HomologicalComplex.quasiIso A (.up ℤ)) := by
  apply (derives F).isRightDerivedFunctor_of_isIso (diagramUnit F)
  intro I
  exact diagramUnit_isIso F I.obj I.property

private theorem diagramUnit_isIso_of_other
    (RF : DerivedCategory.{w} A ⥤ DerivedCategory.{w} B)
    (eta : F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q.{w} ⟶
      DerivedCategory.Q.{w} ⋙ RF)
    (hRF : RF.IsRightDerivedFunctor eta (HomologicalComplex.quasiIso A (.up ℤ)))
    (I : CochainComplex A ℤ) (hI : IsIso (eta.app I)) :
    IsIso (F.rightDerivedFunctorUnitQ I) := by
  let := hRF
  let := diagramUnit_isDerived F
  let e := Functor.rightDerivedUnique RF F.rightDerivedFunctor eta (diagramUnit F)
    (HomologicalComplex.quasiIso A (.up ℤ))
  have he := Functor.rightDerivedNatTrans_app RF F.rightDerivedFunctor eta (diagramUnit F)
    (HomologicalComplex.quasiIso A (.up ℤ)) (Iso.refl _).hom I
  have hh : eta.app I ≫ e.hom.app (DerivedCategory.Q.obj I) = (diagramUnit F).app I := by
    simpa only [e, Functor.rightDerivedUnique, Functor.rightDerivedNatIso, Iso.refl,
      NatTrans.id_app, Category.id_comp] using he
  change IsIso ((diagramUnit F).app I)
  rw [← hh]
  let := hI
  infer_instance
end

section
variable {A B Ap Bp : Type (u + 1)}
    [Category.{u} A] [Category.{u} B] [Category.{u} Ap] [Category.{u} Bp]
    [Abelian A] [Abelian B] [Abelian Ap] [Abelian Bp]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} Ap] [HasDerivedCategory.{w} Bp]
    [HasKInjectiveResolutions A] [HasKInjectiveResolutions Ap]
    (F : A ⥤ B) (G : Ap ⥤ Bp) (x : A ⥤ Ap) (y : B ⥤ Bp)
    [F.Additive] [G.Additive] [x.Additive] [y.Additive]
    [PreservesFiniteLimits x] [PreservesFiniteColimits x]
    [PreservesFiniteLimits y] [PreservesFiniteColimits y]

/-- An acyclic exact square has a unique comparison normalized by right-derived units.
Source: Stacks 0D6E, uniqueness of right derivation.
(blueprint: lem-pur-algebra-diagram-normalized-derived-square).
Proof: apply the right-derived comparison universal property to the ordinary square.
The source unit is invertible on K-injectives, and the hypothesis says that the target
unit is invertible after the horizontal functor on those complexes. Exact localization
factors convert its normalization to the displayed equation. Uniqueness follows from
the same universal property. -/
theorem algebraDiagramNormalizedDerivedSquare
    (hG : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj I)))
    (c : F ⋙ y ≅ x ⋙ G) :
    ∃! b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
        x.mapDerivedCategory ⋙ G.rightDerivedFunctor,
      AlgebraDiagramDerivedSquareNormalized F G x y c b := by
  obtain ⟨b, hb, hu⟩ := derivedCoefficientComparison F G x y
    x.mapDerivedCategory y.mapDerivedCategory x.mapDerivedCategoryFactors
    y.mapDerivedCategoryFactors F.rightDerivedFunctor G.rightDerivedFunctor
    (diagramUnit F) (diagramUnit G) (diagramUnit_isIso F) hG c
  have iff_norm (k : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor) :
      AlgebraDiagramDerivedSquareNormalized F G x y c k ↔
      ∀ M : CochainComplex A ℤ,
        y.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
            y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M) ≫
            k.hom.app (DerivedCategory.Q.obj M) =
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
            G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M) ≫
            G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.inv.app M) := by
    constructor
    · intro h M
      have hh := h M
      apply (cancel_epi (y.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj M))).mp
      apply (cancel_mono (G.rightDerivedFunctor.map
        (x.mapDerivedCategoryFactors.hom.app M))).mp
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
        ← Functor.map_comp, Iso.inv_hom_id_app] at *
      erw [Functor.map_id, Category.comp_id]
      exact hh
    · intro h M
      have hh := h M
      have hh' := congrArg (fun f => y.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫ f ≫
          G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app M)) hh
      simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
        ← Functor.map_comp, Iso.inv_hom_id_app] at hh'
      erw [Functor.map_id, Category.comp_id] at hh'
      exact hh'
  refine ⟨b, (iff_norm b).2 hb, ?_⟩
  intro k hk
  exact hu k ((iff_norm k).1 hk)
private theorem diagramSquare_unit_iff
    (c : F ⋙ y ≅ x ⋙ G)
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ≅
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (h : AlgebraDiagramDerivedSquareNormalized F G x y c b)
    (M : CochainComplex A ℤ) :
    IsIso (y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M)) ↔
      IsIso (G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M)) := by
  have hh := h M
  have hleft : IsIso (y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M) ≫
      b.hom.app (DerivedCategory.Q.obj M) ≫
      G.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app M)) ↔
      IsIso (y.mapDerivedCategory.map (F.rightDerivedFunctorUnitQ M)) := by
    exact isIso_comp_right_iff _ _
  have hright : IsIso (y.mapDerivedCategoryFactors.hom.app
        ((F.mapHomologicalComplex (.up ℤ)).obj M) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) ≫
      G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M)) ↔
      IsIso (G.rightDerivedFunctorUnitQ ((x.mapHomologicalComplex (.up ℤ)).obj M)) := by
    have : IsIso ((NatTrans.mapHomologicalComplex c.hom (.up ℤ)).app M) :=
      inferInstanceAs (IsIso ((NatIso.mapHomologicalComplex c (.up ℤ)).hom.app M))
    rw [isIso_comp_left_iff, isIso_comp_left_iff]
  exact hleft.symm.trans ((congrArg IsIso hh).to_iff.trans hright)

end
private theorem diagramConstantEvaluation_kinjective
    {J C : Type u} [SmallCategory J] [SmallCategory C]
    (K : GrothendieckTopology C) (R : Sheaf K RingCat.{u}) (j : J)
    (I : CochainComplex (ringedSiteModules.{u} (diagramSiteRing J C K R)) ℤ)
    (hI : I.IsKInjective) :
    CochainComplex.IsKInjective
      (((algebraDiagramEvaluation (diagramSiteRing J C K R) j).mapHomologicalComplex
        (.up ℤ)).obj I) := by
  classical
  let A := ringedSiteModules.{u} R
  let := SheafOfModules.isGrothendieckAbelian R
  let G := evaluationLeftAdjoint A j
  have (k : J) : PreservesFiniteLimits (G ⋙ (evaluation J A).obj k) := by
    let := IsGrothendieckAbelian.hasExactColimitsOfShape_discrete A (j ⟶ k)
    let e : G ⋙ (evaluation J A).obj k ≅
        Functor.const (Discrete (j ⟶ k)) ⋙ colim :=
      NatIso.ofComponents (fun X ↦ Iso.refl _) (by
        intro X Y f
        apply Sigma.hom_ext
        intro i
        simp [G, evaluationLeftAdjoint]
        rfl)
    exact preservesFiniteLimits_of_natIso e.symm
  have : PreservesFiniteLimits G := ⟨fun T _ _ ↦
    preservesLimitsOfShape_of_evaluation G T (fun k ↦ inferInstance)⟩
  have : G.Additive := leftExactFunctor_le_additiveFunctor A (J ⥤ A) G
    (by rw [leftExactFunctor_iff]; infer_instance)
  have : G.IsLeftAdjoint := (evaluationAdjunctionRight A j).isLeftAdjoint
  have : (evaluationLeftAdjoint A j).PreservesHomology := inferInstanceAs G.PreservesHomology
  have := (evaluationAdjunctionRight A j).preservesKInjectiveComplexes
  let E := diagramSiteModuleEquivalence J C K R
  have : E.functor.Additive := by
    constructor
    intro M N f g
    ext k U x
    rfl
  have : E.functor.PreservesKInjectiveComplexes := inferInstance
  let := hI
  change CochainComplex.IsKInjective
    (((E.functor ⋙ (evaluation J A).obj j).mapHomologicalComplex (.up ℤ)).obj I)
  have hE : CochainComplex.IsKInjective
      ((E.functor.mapHomologicalComplex (.up ℤ)).obj I) := inferInstance
  change CochainComplex.IsKInjective
    ((((evaluation J A).obj j).mapHomologicalComplex (.up ℤ)).obj
      ((E.functor.mapHomologicalComplex (.up ℤ)).obj I))
  infer_instance

private theorem restriction_reflects {C : Type u} [SmallCategory C]
    {K : GrothendieckTopology C} {R S : Sheaf K RingCat.{u}} (a : R ⟶ S) :
    (SheafOfModules.restrictScalars.{u} a).ReflectsIsomorphisms := by
  have : (SheafOfModules.restrictScalars.{u} a ⋙
      SheafOfModules.toSheaf.{u} R).ReflectsIsomorphisms := inferInstanceAs
    (SheafOfModules.toSheaf.{u} S).ReflectsIsomorphisms
  exact reflectsIsomorphisms_of_comp (SheafOfModules.restrictScalars.{u} a)
    (SheafOfModules.toSheaf.{u} R)

private theorem diagramExactDerived_reflectsIso
    {A B : Type (u + 1)} [Category.{u} A] [Category.{u} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms := by
  constructor
  intro X Y f hf
  rw [DerivedCategory.isIso_iff]
  intro n
  have : IsIso (F.map ((DerivedCategory.homologyFunctor A n).map f)) :=
    (NatIso.isIso_map_iff (F.mapDerivedCategoryHomologyFunctorIso n) f).2
      (by change IsIso ((DerivedCategory.homologyFunctor B n).map
            (F.mapDerivedCategory.map f)); infer_instance)
  exact isIso_of_reflects_iso _ F

private theorem diagramConstantRing_comm {C : Type u} [SmallCategory C]
    (K : GrothendieckTopology C) (A : CommRingCat.{u}) (U : Cᵒᵖ)
    (a b : (algebraDiagramConstantRing K A).obj.obj U) : a * b = b * a := by
  let : K.PreservesSheafification (forget₂ CommRingCat.{u} RingCat.{u}) := by
    constructor
    intro P Q f hf
    change K.W (Functor.whiskerRight f (forget₂ CommRingCat.{u} RingCat.{u}))
    rw [K.W_iff_isLocallyBijective] at hf ⊢
    constructor
    · apply (Presheaf.isLocallyInjective_forget_iff K _).mp
      exact (Presheaf.isLocallyInjective_forget_iff K f).mpr hf.1
    · apply (Presheaf.isLocallySurjective_iff_whisker_forget K _).mpr
      exact (Presheaf.isLocallySurjective_iff_whisker_forget K f).mp hf.2
  let e := (constantCommuteCompose K (forget₂ CommRingCat.{u} RingCat.{u})).app A
  let f := e.inv.hom.app U
  have hf : Function.Injective f := (ConcreteCategory.bijective_of_isIso f).1
  apply hf
  rw [map_mul, map_mul]
  exact @mul_comm (((constantSheaf K CommRingCat).obj A).obj.obj U) inferInstance (f a) (f b)

private theorem diagramRestrictionDerived
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {K : GrothendieckTopology C} {L : GrothendieckTopology D}
    {AX BX : Sheaf K RingCat.{u}} {AY BY : Sheaf L RingCat.{u}}
    (hAX : ∀ (U : Cᵒᵖ) (a b : AX.obj.obj U), a * b = b * a)
    (hBX : ∀ (U : Cᵒᵖ) (a b : BX.obj.obj U), a * b = b * a)
    (hAY : ∀ (U : Dᵒᵖ) (a b : AY.obj.obj U), a * b = b * a)
    (aX : AX ⟶ BX) (aY : AY ⟶ BY)
    (f : RingedToposMorphism BX BY) (g : RingedToposMorphism AX AY)
    [HasDerivedCategory.{w} (ringedSiteModules.{u} AX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} BX)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} AY)]
    [HasDerivedCategory.{w} (ringedSiteModules.{u} BY)]
    (c : f.modules ⋙ SheafOfModules.restrictScalars.{u} aY ≅
      SheafOfModules.restrictScalars.{u} aX ⋙ g.modules) :
    ∃ d : f.modules.rightDerivedFunctor ⋙
        (SheafOfModules.restrictScalars.{u} aY).mapDerivedCategory ≅
      (SheafOfModules.restrictScalars.{u} aX).mapDerivedCategory ⋙
        g.modules.rightDerivedFunctor,
      AlgebraDiagramDerivedSquareNormalized f.modules g.modules
        (SheafOfModules.restrictScalars.{u} aX)
        (SheafOfModules.restrictScalars.{u} aY) c d := by
  obtain ⟨RF, eta, hRF, _, hacyc⟩ := coefficientAcyclicDerived AX BX AY
    hAX hBX hAY aX g
  have hG (I : CochainComplex (ringedSiteModules.{u} BX) ℤ) (hI : I.IsKInjective) :
      IsIso (g.modules.rightDerivedFunctorUnitQ
        (((SheafOfModules.restrictScalars.{u} aX).mapHomologicalComplex (.up ℤ)).obj I)) :=
    diagramUnit_isIso_of_other g.modules RF eta hRF _ (hacyc I hI)
  exact (algebraDiagramNormalizedDerivedSquare f.modules g.modules
    (SheafOfModules.restrictScalars.{u} aX) (SheafOfModules.restrictScalars.{u} aY) hG c).exists

end CategoryTheory
