/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q02 and K9
-/
module

public import Sheaf.AlgebraicGeometry.SupportLocalizationTriangle
public import Sheaf.CategoryTheory.DerivedInjectiveBoundary
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import Mathlib.Algebra.Homology.ConcreteCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Sheaf.AlgebraicGeometry.ProEtalePairFlasque
public import Sheaf.AlgebraicGeometry.SupportTriangleConstruction
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import Sheaf.AlgebraicGeometry.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact
import WeilConjectures.CategoryTheory.Abelian.SplitSESBoundaryComparison
import Sheaf.AlgebraicGeometry.ProEtaleInjectiveSupportGlobalModel
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # The global boundary of the pro-etale support triangle

Source: Stacks Project, etale-cohomology.tex, Tag 09XP, section-cohomology-support;
derived.tex, Tag 014Z, section-canonical-delta-functor
(blueprint: lem-pur-proetale-support-global-boundary).

## Main statements

* `supportGlobalTriangleComparison` compares all three arrows, using the canonical
  right-derived units and the sectionwise kernel inclusion.
* `supportGlobalBoundaryNormalization` identifies the resulting boundary with the
  natural supported-cohomology boundary, including its cocycle formula with no extra sign.

All coefficients are ordinary constant-ring module sheaves, with no constructibility condition.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open CategoryTheory.Abelian

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorPlus
  DerivedCategory.Q DerivedCategory.Qh DerivedCategory.quotientCompQhIso

namespace AlgebraicGeometry.ProEtale

-- The canonical-unit argument from DerivedDirectImageKInjectiveShiftComparison,
-- used here generically for evaluation rather than for ringed-space direct image.
set_option backward.isDefEq.respectTransparency false in
private theorem unitCommShiftAll
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] : NatTrans.CommShift F.rightDerivedFunctorUnit ℤ := by
  let inj := ObjectProperty.ι (HomotopyCategory.subcategoryAcyclic C).rightOrthogonal
  let E := HomotopyCategory.KInjectives.equivalence C
  let G := inj ⋙ F.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  have hI : NatTrans.CommShift F.rightDerivedFunctorIsoKInjectives.inv ℤ :=
    Functor.CommShift.ofIso_compatibility F.rightDerivedFunctorIsoKInjectives.symm ℤ
  have hinv (Y : DerivedCategory C) :
      F.rightDerivedFunctorIsoKInjectives.inv.app Y =
        F.rightDerivedFunctorUnit.app (inj.obj (E.inverse.obj Y)) ≫
          F.rightDerivedFunctor.map (E.counit.app Y) := by
    simp [Functor.rightDerivedFunctorIsoKInjectives, inj, E]
  have heq : Functor.whiskerLeft inj F.rightDerivedFunctorUnit =
      (Functor.leftUnitor G).inv ≫ Functor.whiskerRight E.unitIso.hom G ≫
        (Functor.associator E.functor E.inverse G).hom ≫
        Functor.whiskerLeft E.functor F.rightDerivedFunctorIsoKInjectives.inv ≫
        (Functor.associator inj DerivedCategory.Qh F.rightDerivedFunctor).hom := by
    ext X
    have hn := F.rightDerivedFunctorUnit.naturality (inj.map (E.unit.app X))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.leftUnitor_inv_app, hinv]
    dsimp only [G, E, inj] at hn ⊢
    simp only [Category.id_comp, Category.assoc]
    rw [← Category.assoc]
    erw [hn]
    erw [Category.comp_id]
    simp only [Functor.comp_map, Category.assoc]
    change _ = _ ≫ F.rightDerivedFunctor.map (E.functor.map (E.unit.app X)) ≫
      F.rightDerivedFunctor.map (E.counit.app (E.functor.obj X))
    rw [← Functor.map_comp]
    erw [E.functor_unit_comp, CategoryTheory.Functor.map_id, Category.comp_id]
    rfl
  have : NatTrans.CommShift (Functor.whiskerLeft inj F.rightDerivedFunctorUnit) ℤ := by
    rw [heq]
    dsimp only [G, E, inj]
    infer_instance
  refine NatTrans.CommShift.of_whiskerLeft _ inj (fun K ↦ ?_)
  let J := E.inverse.obj (DerivedCategory.Qh.obj K)
  obtain ⟨f, hf⟩ := (J.property.map_bijective_of_isTriangulated DerivedCategory.Qh
    K).surjective
      (E.counitIso.inv.app (DerivedCategory.Qh.obj K))
  refine ⟨J, f, ?_⟩
  rw [Functor.comp_map, hf]
  infer_instance


section GlobalGeneric
universe v w
variable {C : Type v} {D : Type w} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]

private def globalUnitComparison (F : C ⥤ D) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor :=
  (Functor.isoWhiskerLeft (F.mapHomologicalComplex (.up ℤ))
    (DerivedCategory.quotientCompQhIso _)).inv ≫
  (Functor.associator _ _ _).inv ≫
  (Functor.isoWhiskerRight (F.mapHomotopyCategoryFactors (.up ℤ))
    DerivedCategory.Qh).inv ≫
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (HomotopyCategory.quotient _ _) F.rightDerivedFunctorUnit ≫
  (Functor.associator _ _ _).inv ≫
  (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _)
    F.rightDerivedFunctor).hom

private theorem globalUnitComparison_app (F : C ⥤ D) [F.Additive]
    (K : CochainComplex C ℤ) [K.IsKInjective] :
    (globalUnitComparison F).app K = (F.rightDerivedFunctorObjQIso K).inv := by
  simp [globalUnitComparison, Functor.rightDerivedFunctorObjQIso,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]

set_option backward.isDefEq.respectTransparency false in
private theorem globalUnitComparison_shift (F : C ⥤ D) [F.Additive] :
    NatTrans.CommShift (globalUnitComparison F) ℤ := by
  have := unitCommShiftAll F
  have : NatTrans.CommShift (DerivedCategory.quotientCompQhIso D).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  have : NatTrans.CommShift (F.mapHomotopyCategoryFactors (.up ℤ)).inv ℤ :=
    NatTrans.CommShift.of_iso_inv _ _
  dsimp only [globalUnitComparison]
  simp only [Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerRight_hom]
  infer_instance

private theorem inverseShiftedNaturality
    {B E : Type*} [Category B] [Category E] [HasShift B ℤ] [HasShift E ℤ]
    {F G : B ⥤ E} [F.CommShift ℤ] [G.CommShift ℤ]
    (τ : F ⟶ G) [NatTrans.CommShift τ ℤ] {K L : B}
    [IsIso (τ.app K)] [IsIso (τ.app L)] (f : K ⟶ L⟦(1 : ℤ)⟧) :
    ShiftedHom.map f G ≫ (inv (τ.app L))⟦(1 : ℤ)⟧' =
      inv (τ.app K) ≫ ShiftedHom.map f F := by
  have h := ShiftedHom.map_naturality f τ
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at h
  apply (cancel_epi (τ.app K)).1
  simp only [IsIso.hom_inv_id_assoc]
  rw [← reassoc_of% h, ← Functor.map_comp]
  simp

private def globalSplitting {S : ShortComplex (CochainComplex C ℤ)}
    (hS : S.ShortExact) [∀ n : ℤ, Injective (S.X₁.X n)] (n : ℤ) :
    (S.map (HomologicalComplex.eval C (.up ℤ) n)).Splitting := by
  have : Injective ((S.map (HomologicalComplex.eval C (.up ℤ) n)).X₁) :=
    inferInstanceAs (Injective (S.X₁.X n))
  exact ShortComplex.ShortExact.splittingOfInjective
    ((HomologicalComplex.shortExact_iff_degreewise_shortExact S).mp hS n)

private theorem globalMappedShortExact (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)] :
    (S.map (F.mapHomologicalComplex (.up ℤ))).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact ((globalSplitting hS n).map F).shortExact

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private def globalDerivedTriangleIso (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective] :
    F.rightDerivedFunctor.mapTriangle.obj (DerivedCategory.triangleOfSES hS) ≅
      DerivedCategory.triangleOfSES (globalMappedShortExact F hS) := by
  refine Triangle.isoMk _ _ (F.rightDerivedFunctorObjQIso S.X₁)
    (F.rightDerivedFunctorObjQIso S.X₂) (F.rightDerivedFunctorObjQIso S.X₃) ?_ ?_ ?_
  · exact F.rightDerivedFunctor_map_Q_map_comp_objQIso_hom S.f
  · exact F.rightDerivedFunctor_map_Q_map_comp_objQIso_hom S.g
  · let σ := globalSplitting hS
    let σF (n : ℤ) := (σ n).map F
    have hd : ShiftedHom.map (CochainComplex.homOfDegreewiseSplit S σ)
        (F.mapHomologicalComplex (.up ℤ)) =
      CochainComplex.homOfDegreewiseSplit (S.map (F.mapHomologicalComplex (.up ℤ))) σF := by
      ext n
      simp [ShiftedHom.map, CochainComplex.cocycleOfDegreewiseSplit, σF, Functor.map_comp]
    have := globalUnitComparison_shift F
    have hIso (K : CochainComplex C ℤ) [K.IsKInjective] :
        IsIso ((globalUnitComparison F).app K) := by
      rw [globalUnitComparison_app]
      infer_instance
    have hn := inverseShiftedNaturality (globalUnitComparison F)
      (CochainComplex.homOfDegreewiseSplit S σ)
    have hinv (K : CochainComplex C ℤ) [K.IsKInjective] :
        inv ((globalUnitComparison F).app K) = (F.rightDerivedFunctorObjQIso K).hom := by
      apply IsIso.inv_eq_of_hom_inv_id
      rw [globalUnitComparison_app]
      exact Iso.inv_hom_id _
    rw [hinv, hinv] at hn
    change ShiftedHom.map (DerivedCategory.triangleOfSESδ hS) F.rightDerivedFunctor ≫
      (F.rightDerivedFunctorObjQIso S.X₁).hom⟦(1 : ℤ)⟧' =
        (F.rightDerivedFunctorObjQIso S.X₃).hom ≫
          DerivedCategory.triangleOfSESδ (globalMappedShortExact F hS)
    rw [DerivedCategory.triangleOfSESδ_eq_degreewiseSplit S hS σ,
      DerivedCategory.triangleOfSESδ_eq_degreewiseSplit _ (globalMappedShortExact F hS) σF]
    simpa only [ShiftedHom.comp_map, hd] using hn

private theorem globalDerivedTriangleIso_hom₁ (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective] :
    (globalDerivedTriangleIso F hS).hom.hom₁ =
      (F.rightDerivedFunctorObjQIso S.X₁).hom := rfl

private theorem globalDerivedTriangleIso_hom₂ (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective] :
    (globalDerivedTriangleIso F hS).hom.hom₂ =
      (F.rightDerivedFunctorObjQIso S.X₂).hom := rfl

private theorem globalDerivedTriangleIso_hom₃ (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective] :
    (globalDerivedTriangleIso F hS).hom.hom₃ =
      (F.rightDerivedFunctorObjQIso S.X₃).hom := rfl

attribute [local irreducible] globalDerivedTriangleIso

private def globalTransportTriangleIso (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective]
    {T : ShortComplex (CochainComplex D ℤ)} (hT : T.ShortExact)
    (e : S.map (F.mapHomologicalComplex (.up ℤ)) ≅ T) :
    F.rightDerivedFunctor.mapTriangle.obj (DerivedCategory.triangleOfSES hS) ≅
      DerivedCategory.triangleOfSES hT := by
  let t := DerivedCategory.triangleOfSES.map (globalMappedShortExact F hS) hT e.hom
  have : IsIso t := Triangle.isIso_of_isIsos t
    (inferInstanceAs (IsIso (DerivedCategory.Q.map e.hom.τ₁)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map e.hom.τ₂)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map e.hom.τ₃)))
  exact globalDerivedTriangleIso F hS ≪≫ asIso t

private theorem globalTransportTriangleIso_hom₁ (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective]
    {T : ShortComplex (CochainComplex D ℤ)} (hT : T.ShortExact)
    (e : S.map (F.mapHomologicalComplex (.up ℤ)) ≅ T) :
    (globalTransportTriangleIso F hS hT e).hom.hom₁ =
      (F.rightDerivedFunctorObjQIso S.X₁).hom ≫ DerivedCategory.Q.map e.hom.τ₁ := by
  change (globalDerivedTriangleIso F hS).hom.hom₁ ≫
    DerivedCategory.Q.map e.hom.τ₁ = _
  rw [globalDerivedTriangleIso_hom₁]

private theorem globalTransportTriangleIso_hom₂ (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective]
    {T : ShortComplex (CochainComplex D ℤ)} (hT : T.ShortExact)
    (e : S.map (F.mapHomologicalComplex (.up ℤ)) ≅ T) :
    (globalTransportTriangleIso F hS hT e).hom.hom₂ =
      (F.rightDerivedFunctorObjQIso S.X₂).hom ≫ DerivedCategory.Q.map e.hom.τ₂ := by
  change (globalDerivedTriangleIso F hS).hom.hom₂ ≫
    DerivedCategory.Q.map e.hom.τ₂ = _
  rw [globalDerivedTriangleIso_hom₂]

private theorem globalTransportTriangleIso_hom₃ (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective]
    {T : ShortComplex (CochainComplex D ℤ)} (hT : T.ShortExact)
    (e : S.map (F.mapHomologicalComplex (.up ℤ)) ≅ T) :
    (globalTransportTriangleIso F hS hT e).hom.hom₃ =
      (F.rightDerivedFunctorObjQIso S.X₃).hom ≫ DerivedCategory.Q.map e.hom.τ₃ := by
  change (globalDerivedTriangleIso F hS).hom.hom₃ ≫
    DerivedCategory.Q.map e.hom.τ₃ = _
  rw [globalDerivedTriangleIso_hom₃]

attribute [local irreducible] globalTransportTriangleIso

private def convertSequenceTriangleIso
    (F : DerivedCategory C ⥤ DerivedCategory D) [F.CommShift ℤ]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    {T : ShortComplex (CochainComplex D ℤ)} (hT : T.ShortExact)
    (hq : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)))
    (hqT : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex T)))
    (t : F.mapTriangle.obj (DerivedCategory.triangleOfSES hS) ≅
      DerivedCategory.triangleOfSES hT) :
    F.mapTriangle.obj (supportSequenceTriangle S hq) ≅ supportSequenceTriangle T hqT := t

attribute [local irreducible] convertSequenceTriangleIso

private def globalSequenceTriangleIso (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective]
    {T : ShortComplex (CochainComplex D ℤ)} (hT : T.ShortExact)
    (hq : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)))
    (hqT : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex T)))
    (e : S.map (F.mapHomologicalComplex (.up ℤ)) ≅ T) :
    F.rightDerivedFunctor.mapTriangle.obj (supportSequenceTriangle S hq) ≅
      supportSequenceTriangle T hqT :=
  convertSequenceTriangleIso F.rightDerivedFunctor hS hT hq hqT
    (globalTransportTriangleIso F hS hT e)


private theorem globalSequenceTriangleIso_hom₁ (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective]
    {T : ShortComplex (CochainComplex D ℤ)} (hT : T.ShortExact)
    (hq : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)))
    (hqT : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex T)))
    (e : S.map (F.mapHomologicalComplex (.up ℤ)) ≅ T) :
    (globalSequenceTriangleIso F hS hT hq hqT e).hom.hom₁ =
      (F.rightDerivedFunctorObjQIso S.X₁).hom ≫ DerivedCategory.Q.map e.hom.τ₁ := by
  unfold globalSequenceTriangleIso convertSequenceTriangleIso
  change (globalTransportTriangleIso F hS hT e).hom.hom₁ = _
  exact globalTransportTriangleIso_hom₁ F hS hT e

private theorem globalSequenceTriangleIso_hom₂ (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective]
    {T : ShortComplex (CochainComplex D ℤ)} (hT : T.ShortExact)
    (hq : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)))
    (hqT : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex T)))
    (e : S.map (F.mapHomologicalComplex (.up ℤ)) ≅ T) :
    (globalSequenceTriangleIso F hS hT hq hqT e).hom.hom₂ =
      (F.rightDerivedFunctorObjQIso S.X₂).hom ≫ DerivedCategory.Q.map e.hom.τ₂ := by
  unfold globalSequenceTriangleIso convertSequenceTriangleIso
  change (globalTransportTriangleIso F hS hT e).hom.hom₂ = _
  exact globalTransportTriangleIso_hom₂ F hS hT e

private theorem globalSequenceTriangleIso_hom₃ (F : C ⥤ D) [F.Additive]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    [∀ n : ℤ, Injective (S.X₁.X n)]
    [S.X₁.IsKInjective] [S.X₂.IsKInjective] [S.X₃.IsKInjective]
    {T : ShortComplex (CochainComplex D ℤ)} (hT : T.ShortExact)
    (hq : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)))
    (hqT : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex T)))
    (e : S.map (F.mapHomologicalComplex (.up ℤ)) ≅ T) :
    (globalSequenceTriangleIso F hS hT hq hqT e).hom.hom₃ =
      (F.rightDerivedFunctorObjQIso S.X₃).hom ≫ DerivedCategory.Q.map e.hom.τ₃ := by
  unfold globalSequenceTriangleIso convertSequenceTriangleIso
  change (globalTransportTriangleIso F hS hT e).hom.hom₃ = _
  exact globalTransportTriangleIso_hom₃ F hS hT e

end GlobalGeneric

section GlobalShortComplex
universe v
variable {C : Type v} [Category C] [Abelian C]

private def shortComplexIsoFromQuotient
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (b : S.X₂ ≅ T.X₂) (c : S.X₃ ≅ T.X₃) (h : b.hom ≫ T.g = S.g ≫ c.hom) :
    S ≅ T := by
  let a := hT.fIsKernel.lift (KernelFork.ofι (S.f ≫ b.hom) (by
    rw [Category.assoc, h, ← Category.assoc, S.zero, zero_comp]))
  let a' := hS.fIsKernel.lift (KernelFork.ofι (T.f ≫ b.inv) (by
    rw [← cancel_mono c.hom, zero_comp, Category.assoc, Category.assoc, ← h,
      Iso.inv_hom_id_assoc, T.zero]))
  have ha : a ≫ T.f = S.f ≫ b.hom := hT.fIsKernel.fac _ WalkingParallelPair.zero
  have ha' : a' ≫ S.f = T.f ≫ b.inv := hS.fIsKernel.fac _ WalkingParallelPair.zero
  have := hS.mono_f
  have := hT.mono_f
  let aIso : S.X₁ ≅ T.X₁ :=
    { hom := a
      inv := a'
      hom_inv_id := by
        apply (cancel_mono S.f).1
        rw [Category.assoc, ha', ← Category.assoc, ha, Category.assoc,
          Iso.hom_inv_id, Category.comp_id, Category.id_comp]
      inv_hom_id := by
        apply (cancel_mono T.f).1
        rw [Category.assoc, ha, ← Category.assoc, ha', Category.assoc,
          Iso.inv_hom_id, Category.comp_id, Category.id_comp] }
  exact ShortComplex.isoMk aIso b c ha h

private theorem shortComplexIsoFromQuotient_hom₂
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (b : S.X₂ ≅ T.X₂) (c : S.X₃ ≅ T.X₃) (h : b.hom ≫ T.g = S.g ≫ c.hom) :
    (shortComplexIsoFromQuotient hS hT b c h).hom.τ₂ = b.hom := rfl

private theorem shortComplexIsoFromQuotient_hom₃
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (b : S.X₂ ≅ T.X₂) (c : S.X₃ ≅ T.X₃) (h : b.hom ≫ T.g = S.g ≫ c.hom) :
    (shortComplexIsoFromQuotient hS hT b c h).hom.τ₃ = c.hom := rfl

attribute [local irreducible] shortComplexIsoFromQuotient

end GlobalShortComplex

section GlobalIntegerBoundary
universe v
variable {C : Type v} [Category C] [Abelian C] [HasDerivedCategory C]
open CategoryTheory.Category
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- The integer-graded comparison used in Abelian.NatComplexDerivedBoundary.
private theorem integer_boundary (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact) (n : ℤ) :
    DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES hS) n (n+1) rfl ≫
      (DerivedCategory.homologyFunctorFactors C (n+1)).hom.app S.X₁ =
    (DerivedCategory.homologyFunctorFactors C n).hom.app S.X₃ ≫ hS.δ n (n+1) rfl := by
  have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
  have hc := CochainComplex.mappingCone.homologySequenceδ_triangleh hS n (n+1) rfl
  rw [CochainComplex.homologySequenceδ_quotient_mapTriangle_obj] at hc
  have hcc := congrArg
    (fun f ↦ (HomotopyCategory.homologyFunctorFactors C (.up ℤ) n).inv.app _ ≫
      f ≫ (HomotopyCategory.homologyFunctorFactors C (.up ℤ) (n+1)).hom.app _) hc
  dsimp only [CochainComplex.mappingCone.triangle, Pretriangulated.Triangle.mk] at hcc
  simp only [assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app] at hcc
  erw [comp_id, comp_id] at hcc
  apply (cancel_epi ((DerivedCategory.homologyFunctor C n).map
    (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)))).1
  erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc]
  change (DerivedCategory.homologyFunctor C n).map
      (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)) ≫
      (DerivedCategory.homologyFunctor C 0).shiftMap
        (DerivedCategory.triangleOfSESδ hS) n (n+1) (by omega) ≫ _ = _
  have hs := Functor.shiftMap_comp' (DerivedCategory.homologyFunctor C 0)
    (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S))
    (DerivedCategory.triangleOfSESδ hS) n (n+1) (by omega)
  simp only [DerivedCategory.shift_homologyFunctor] at hs
  erw [← reassoc_of% hs, DerivedCategory.descShortComplex_triangleOfSESδ]
  erw [DerivedCategory.shiftMap_homologyFunctor_map_Q _ n (n+1) (by omega)]
  erw [assoc, assoc, Iso.inv_hom_id_app, comp_id]
  simpa only [CochainComplex.mappingCone.triangle, Pretriangulated.Triangle.mk, assoc] using
    congrArg (fun f ↦ (DerivedCategory.homologyFunctorFactors C n).hom.app _ ≫ f) hcc

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem sequenceIntegerBoundary (S : ShortComplex (CochainComplex C ℤ))
    (hS : S.ShortExact)
    (hq : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)))
    (n : ℤ) :
    DerivedCategory.HomologySequence.δ (supportSequenceTriangle S hq) n (n + 1) rfl =
      (DerivedCategory.homologyFunctorFactors C n).hom.app S.X₃ ≫
      hS.δ n (n + 1) rfl ≫
      (DerivedCategory.homologyFunctorFactors C (n + 1)).inv.app S.X₁ := by
  apply (cancel_mono
    ((DerivedCategory.homologyFunctorFactors C (n + 1)).hom.app S.X₁)).1
  change DerivedCategory.HomologySequence.δ (DerivedCategory.triangleOfSES hS)
    n (n + 1) rfl ≫ _ = _
  have h := integer_boundary S hS n
  dsimp only [DerivedCategory.triangleOfSES] at h ⊢
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact h.trans (congrArg
    (fun f ↦ (DerivedCategory.homologyFunctorFactors C n).hom.app S.X₃ ≫ f)
    (Category.comp_id (hS.δ n (n + 1) rfl))).symm

end GlobalIntegerBoundary

section GlobalCocycle
universe v
variable {B : Type v} [Ring B]

private theorem globalCocycleFormula
    (R : ShortComplex (CochainComplex (ModuleCat.{v} B) ℤ)) (hR : R.ShortExact)
    (q : ℤ) (c : R.X₃.X q) (hc : R.X₃.d q (q + 1) c = 0)
    (b : R.X₂.X q) (hb : R.g.f q b = c) :
    ∃ (a : R.X₁.X (q + 1)) (ha : R.X₁.d (q + 1) (q + 1 + 1) a = 0),
      R.f.f (q + 1) a = R.X₂.d q (q + 1) b ∧
      hR.δ q (q + 1) rfl
        (R.X₃.homologyπ q (R.X₃.cyclesMk c (q + 1) (by simp) hc)) =
        R.X₁.homologyπ (q + 1)
          (R.X₁.cyclesMk a (q + 1 + 1) (by simp) ha) := by
  have hdb : R.g.f (q + 1) (R.X₂.d q (q + 1) b) = 0 := by
    rw [← ConcreteCategory.comp_apply, ← R.g.comm q (q + 1),
      ConcreteCategory.comp_apply, hb, hc]
  obtain ⟨a, ha⟩ := (ShortComplex.moduleCat_exact_iff _).mp
    (hR.exact.map (HomologicalComplex.eval _ _ (q + 1))) _ hdb
  have hda := hR.d_eq_zero_of_f_eq_d_apply q (q + 1) b a ha (q + 1 + 1)
  exact ⟨a, hda, ha, hR.δ_apply q (q + 1) rfl c hc b hb a ha
    (q + 1 + 1) (by simp)⟩

end GlobalCocycle


variable (A : Type (u + 1)) [CommRing A] [hA : Finite A]

/-- Evaluation at a specified pro-etale object, using the existing section functor.
Source: Stacks Tag 09XP, section-cohomology-support
(blueprint: lem-pur-proetale-support-global-boundary). -/
abbrev supportGlobalEvaluation {X : Scheme.{u}} (V : X.ProEt) :
    Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A) ⥤ ModuleCat.{u + 1} A :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)

/-- The site arrow for the specified complementary open, rather than a choice of open.
Source: Stacks Tag 09XP, restriction along the complement
(blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalRestriction {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Scheme.ProEt.mk j ⟶ Scheme.ProEt.mk (𝟙 X) :=
  MorphismProperty.Over.homMk j (Category.comp_id j)

/-- The object of X's site underlying the terminal object of the open site.
Source: Stacks Tag 09XP, open-section formula
(blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalOpenObjectIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
        (Scheme.ProEt.mk (𝟙 U)) ≅ Scheme.ProEt.mk j :=
  MorphismProperty.Over.isoMk (Iso.refl U) (by simp)

/-- The canonical section formula `(j^*M)(U) ≅ M(U)`, using the recorded comparison
with open restriction and the identity of the underlying open object.
Source: Stacks Tag 09XP, open-section formula
(blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalOpenSectionIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).obj
        ((upperStar (ModuleCat.{u + 1} A) j).obj M) ≅
      (supportGlobalEvaluation A (Scheme.ProEt.mk j)).obj M :=
  (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).mapIso
      ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).app M) ≪≫
    M.obj.mapIso (supportGlobalOpenObjectIso j).symm.op

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the canonical open-section formula.
Source: Stacks Tag 09XP (blueprint: lem-pur-proetale-support-global-boundary).
Proof: use naturality of the open-restriction comparison, and naturality of a sheaf
morphism at the isomorphism of the two presentations of the open object. -/
theorem supportGlobalOpenSectionIso_naturality {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    {M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)} (f : M ⟶ N) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).map
        ((upperStar (ModuleCat.{u + 1} A) j).map f) ≫
        (supportGlobalOpenSectionIso A j N).hom =
      (supportGlobalOpenSectionIso A j M).hom ≫
        (supportGlobalEvaluation A (Scheme.ProEt.mk j)).map f := by
  have h := congrArg (fun t ↦ t.hom.app (op (Scheme.ProEt.mk (𝟙 U))))
    ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.naturality f)
  dsimp [supportGlobalOpenSectionIso, supportGlobalEvaluation]
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  rw [← Category.assoc]
  erw [h]
  simp only [Category.assoc]
  congr 1
  exact (f.hom.naturality _).symm

/-- The section formula as an isomorphism of functors, hence also of section complexes.
Source: Stacks Tag 09XP (blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalOpenEvaluationIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    upperStar (ModuleCat.{u + 1} A) j ⋙
        supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U)) ≅
      supportGlobalEvaluation A (Scheme.ProEt.mk j) :=
  NatIso.ofComponents (supportGlobalOpenSectionIso A j)
    (supportGlobalOpenSectionIso_naturality A j)

/-- The natural derived identification `RΓ(U,j^*K) ≅ R(I ↦ I(U))(K)`.
It is constructed from the ordinary section formula and the unique unit-compatible
composition comparison. Exactness identifies `Rj^*` with the recorded termwise `j^*`.
Source: Stacks Tag 09XP (blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalOpenDerivedIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategoryPlus ⋙
        (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).rightDerivedFunctorPlus ≅
      (supportGlobalEvaluation A (Scheme.ProEt.mk j)).rightDerivedFunctorPlus :=
  letI : (upperStar (ModuleCat.{u + 1} A) j).PreservesInjectiveObjects :=
    ⟨fun {M} hM ↦
      @injective_upperStar_obj_of_weaklyEtale _ _ _ _ _ _ j _ M hM⟩
  Functor.isoWhiskerRight
      (upperStar (ModuleCat.{u + 1} A) j).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.symm
      (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))).rightDerivedFunctorPlus ≪≫
    Functor.rightDerivedFunctorPlusCompIso' (upperStar (ModuleCat.{u + 1} A) j)
      (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 U))) (supportGlobalOpenEvaluationIso A j)

/-- The zero composite of supported inclusion and restriction on section functors.
Source: Stacks Tag 09XP, kernel-of-restriction formula
(blueprint: lem-pur-proetale-support-global-boundary).
Proof: at each sheaf this is the defining equation of its sectionwise kernel. -/
theorem supportGlobalRestriction_zero {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
        (supportGlobalRestriction j) ≫
      (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
        (supportGlobalRestriction j).op = 0 := by
  apply NatTrans.ext
  funext M
  exact kernel.condition (M.obj.map (supportGlobalRestriction j).op)

/-- The actual row of section complexes: kernel of restriction, sections on X, sections
on U. Its arrows are the kernel inclusion and restriction, not chosen maps.
Source: Stacks Tag 09XP, displayed injective restriction sequence
(blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalRow {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))) :
    ShortComplex (CochainComplex (ModuleCat.{u + 1} A) ℤ) :=
  Functor.injectiveBoundaryRow
    (Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
      (supportGlobalRestriction j))
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X)))
    (supportGlobalEvaluation A (Scheme.ProEt.mk j))
    (Sheaf.supportedSectionsInclusion _ _ (supportGlobalRestriction j))
    ((sheafSections _ _).map (supportGlobalRestriction j).op)
    (supportGlobalRestriction_zero A j) I

universe c v

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
-- The free-presheaf restriction proof from SupportLongExact, with the same universes.
private theorem restriction_epi.{cR, vR, uR}
    {C : Type cR} [Category.{vR} C] (J : GrothendieckTopology C)
    (R : Type (max uR vR)) [Ring R] [HasSheafify J (ModuleCat.{max uR vR} R)]
    (I : Sheaf J (ModuleCat.{max uR vR} R)) [Injective I]
    {W V : C} (j : W ⟶ V) [Mono j] : Epi (I.obj.map j.op) := by
  have : Injective I.obj := Injective.injective_of_adjoint (sheafificationAdjunction J _) I
  let a : (uliftYoneda.{uR}.obj W ⋙ ModuleCat.free R) ⟶
      (uliftYoneda.{uR}.obj V ⋙ ModuleCat.free R) :=
    Functor.whiskerRight (uliftYoneda.{uR}.map j) (ModuleCat.free R)
  have : Mono a := by
    have (T : Cᵒᵖ) : Mono (a.app T) := by
      rw [ModuleCat.mono_iff_injective]
      apply Finsupp.mapDomain_injective
      intro x y h
      apply ULift.ext
      exact (cancel_mono j).1 (congrArg ULift.down h)
    exact NatTrans.mono_of_mono_app a
  rw [ModuleCat.epi_iff_surjective]
  intro s
  let b : (uliftYoneda.{uR}.obj W ⋙ ModuleCat.free R) ⟶ I.obj :=
    { app := fun T ↦ ModuleCat.freeDesc (↾fun g ↦ I.obj.map g.down.op s)
      naturality := by
        intro T T' g
        apply ModuleCat.free_hom_ext
        intro x
        simp only [Functor.comp_map, ConcreteCategory.comp_apply]
        erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        change I.obj.map ((g.unop ≫ x.down).op) s = _
        rw [op_comp, I.obj.map_comp]
        rfl }
  obtain ⟨g, hg⟩ := Injective.factors b a
  refine ⟨g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V))), ?_⟩
  have he := congrArg (fun f ↦ f.app (op W) (ModuleCat.freeMk (ULift.up (𝟙 W)))) hg
  have hn := ConcreteCategory.congr_hom (g.naturality j.op)
    (ModuleCat.freeMk (ULift.up (𝟙 V)))
  have he' : g.app (op W) (ModuleCat.freeMk (ULift.up j)) = s := by
    simpa [a, b, ModuleCat.free_map_apply, ModuleCat.freeDesc_apply] using he
  have hn' : I.obj.map j.op (g.app (op V) (ModuleCat.freeMk (ULift.up (𝟙 V)))) =
      g.app (op W) (ModuleCat.freeMk (ULift.up j)) := by
    simpa [ModuleCat.free_map_apply] using hn.symm
  exact hn'.trans he'


private theorem globalRow_termwise {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) [Injective M] :
    (ShortComplex.mk
      ((Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A) (supportGlobalRestriction j)).app M)
      (((sheafSections _ _).map (supportGlobalRestriction j).op).app M)
      (NatTrans.congr_app (supportGlobalRestriction_zero A j) M)).ShortExact where
  exact := ShortComplex.kernelSequence_exact _
  mono_f := by change Mono (kernel.ι _); infer_instance
  epi_g := by
    have : Mono (supportGlobalRestriction j) :=
      (MorphismProperty.Over.forget @WeaklyEtale ⊤ X ⋙ Over.forget X).mono_of_mono_map
        (inferInstanceAs (Mono j))
    exact restriction_epi.{u + 1, u, u + 1} _ _ M _

private theorem globalRow_shortExact {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] : (supportGlobalRow A j I).ShortExact :=
  Functor.injectiveBoundaryRow_shortExact
    (Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)
      (supportGlobalRestriction j))
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X)))
    (supportGlobalEvaluation A (Scheme.ProEt.mk j))
    (Sheaf.supportedSectionsInclusion _ _ (supportGlobalRestriction j))
    ((sheafSections _ _).map (supportGlobalRestriction j).op)
    (supportGlobalRestriction_zero A j) (globalRow_termwise A j) I

private def globalOpenObjectIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj
      ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj
        (Scheme.ProEt.mk (𝟙 X))) ≅ Scheme.ProEt.mk j :=
  (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).mapIso
    (overPullbackObjMkIdIso j) ≪≫ supportGlobalOpenObjectIso j

private def globalOpenSectionIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).obj
      ((lowerStar (ModuleCat.{u + 1} A) j).obj
        ((upperStar (ModuleCat.{u + 1} A) j).obj M)) ≅
      (supportGlobalEvaluation A (Scheme.ProEt.mk j)).obj M :=
  (supportGlobalEvaluation A
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj
      (Scheme.ProEt.mk (𝟙 X)))).mapIso
        ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).app M) ≪≫
    M.obj.mapIso (globalOpenObjectIso j).symm.op

set_option backward.isDefEq.respectTransparency false in
private theorem globalOpenSectionIso_naturality {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    {M N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)} (f : M ⟶ N) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).map
      ((lowerStar (ModuleCat.{u + 1} A) j).map
        ((upperStar (ModuleCat.{u + 1} A) j).map f)) ≫
      (globalOpenSectionIso A j N).hom =
    (globalOpenSectionIso A j M).hom ≫
      (supportGlobalEvaluation A (Scheme.ProEt.mk j)).map f := by
  have h := congrArg (fun t ↦ t.hom.app (op
    ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj
      (Scheme.ProEt.mk (𝟙 X)))))
    ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.naturality f)
  dsimp [globalOpenSectionIso, supportGlobalEvaluation]
  dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  rw [lowerStar_map_hom_app, ← Category.assoc]
  erw [h]
  simp only [Category.assoc]
  congr 1
  exact (f.hom.naturality _).symm

private def globalOpenEvaluationIso {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] :
    (upperStar (ModuleCat.{u + 1} A) j ⋙ lowerStar (ModuleCat.{u + 1} A) j) ⋙
      supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X)) ≅
        supportGlobalEvaluation A (Scheme.ProEt.mk j) :=
  NatIso.ofComponents (globalOpenSectionIso A j) (globalOpenSectionIso_naturality A j)

set_option backward.isDefEq.respectTransparency false in
private theorem globalOpenSectionIso_unit {X U : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j]
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app M) ≫
        (globalOpenSectionIso A j M).hom = M.obj.map (supportGlobalRestriction j).op := by
  have h := congrArg (fun t ↦ t.hom.app (op (Scheme.ProEt.mk (𝟙 X))))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit_leftAdjointUniq_hom_app
      (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j) M)
  change (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.app M).hom.app
      (op (Scheme.ProEt.mk (𝟙 X))) ≫
    ((upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j).hom.app M).hom.app
      (op ((MorphismProperty.Over.pullback @WeaklyEtale ⊤ j).obj
        (Scheme.ProEt.mk (𝟙 X)))) = _) at h
  dsimp [globalOpenSectionIso, supportGlobalEvaluation]
  rw [← Category.assoc]
  erw [h]
  change M.obj.map
    ((MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance
      trivial).counit.app (Scheme.ProEt.mk (𝟙 X))).op ≫
        M.obj.map (globalOpenObjectIso j).op.inv = _
  rw [← M.obj.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  change (globalOpenObjectIso j).inv ≫
      (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j inferInstance
        trivial).counit.app (Scheme.ProEt.mk (𝟙 X)) = supportGlobalRestriction j
  exact (Scheme.ProEt.isTerminalMkId X).hom_ext _ _

variable {X Z U : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
  [hi : IsClosedImmersion i] [IsOpenImmersion j] [hqc : QuasiCompact j]
  (hPair : IsCompl (Set.range i) (Set.range j))

private theorem globalSupportTerms
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] (r : ℤ) :
    Injective ((supportedSectionsComplex A i j hPair I.obj).X r) := by
  obtain ⟨_, _, hinj, _⟩ := proEtaleInjectiveSupportGlobalModel A i j hPair
  have : (lowerStar (ModuleCat.{u + 1} A) i).PreservesInjectiveObjects :=
    Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
  change Injective ((lowerStar (ModuleCat.{u + 1} A) i).obj
    ((finiteClosedUpperShriek A i j).obj (I.obj.X r)))
  exact Functor.injective_obj_of_injective (lowerStar (ModuleCat.{u + 1} A) i)
    (hinj.injective_obj
    (inferInstanceAs (Injective (I.obj.X r))))

/-- All three sheaf models used to compute derived global sections are K-injective.
Source: Stacks Tag 09XP, support-injective lemma and restriction sequence
(blueprint: lem-pur-proetale-support-global-boundary).
Proof: the support right adjoint preserves injectives because closed direct image is
exact. Closed and open direct images preserve injectives because their inverse images
are exact. Open restriction preserves injectives because extension by zero is exact.
These additive functors preserve the lower bound. Apply the bounded-below injective
K-injectivity lemma to the resulting complexes. -/
theorem supportGlobalModels_kInjective
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] :
    I.obj.IsKInjective ∧
      (supportedSectionsComplex A i j hPair I.obj).IsKInjective ∧
      CochainComplex.IsKInjective (supportCComplex A j I.obj) := by
  obtain ⟨n, hn⟩ := I.property
  have := hn
  obtain ⟨adj, _, hinj, _⟩ := proEtaleInjectiveSupportGlobalModel A i j hPair
  have := hinj
  have : (lowerStar (ModuleCat.{u + 1} A) i).PreservesInjectiveObjects :=
    Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i)
  have : (lowerStar (ModuleCat.{u + 1} A) j).PreservesInjectiveObjects :=
    Adjunction.preservesInjectiveObjects_of_preservesFiniteLimits
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j)
  have hS (r : ℤ) : Injective ((supportedSectionsComplex A i j hPair I.obj).X r) := by
    change Injective ((lowerStar (ModuleCat.{u + 1} A) i).obj
      ((finiteClosedUpperShriek A i j).obj (I.obj.X r)))
    exact Functor.injective_obj_of_injective (lowerStar (ModuleCat.{u + 1} A) i)
      (hinj.injective_obj (inferInstanceAs
      (Injective (I.obj.X r))))
  have hC (r : ℤ) : Injective ((supportCComplex A j I.obj).X r) := by
    change Injective ((lowerStar (ModuleCat.{u + 1} A) j).obj
      ((upperStar (ModuleCat.{u + 1} A) j).obj (I.obj.X r)))
    exact Functor.injective_obj_of_injective (lowerStar (ModuleCat.{u + 1} A) j)
      (injective_upperStar_obj_of_weaklyEtale (ModuleCat.{u + 1} A) j (I.obj.X r))
  have hSG : (supportedSectionsComplex A i j hPair I.obj).IsStrictlyGE n := by
    dsimp [supportedSectionsComplex]
    infer_instance
  have hCG : CochainComplex.IsStrictlyGE (supportCComplex A j I.obj) n := by
    dsimp [supportCComplex]
    infer_instance
  exact ⟨CochainComplex.isKInjective_of_injective _ n,
    CochainComplex.isKInjective_of_injective _ n,
    CochainComplex.isKInjective_of_injective _ n⟩

/-- The canonical inverse derived-unit comparison on a K-injective model.
Source: Stacks Tags 05TI and 05TH, used in Tag 09XP
(blueprint: lem-pur-proetale-support-global-boundary). -/
def supportGlobalUnitIso
    (J : SupportComplex A X) (hJ : J.IsKInjective) :
    (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctor.obj
        (DerivedCategory.Q.obj J) ≅
      DerivedCategory.Q.obj
        (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
          (.up ℤ)).obj J) :=
  letI := hJ
  (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctorObjQIso J

section TriangleComparison

attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  globalDerivedTriangleIso globalTransportTriangleIso globalSequenceTriangleIso
  shortComplexIsoFromQuotient
  Functor.rightDerivedFunctorObjQIso supportedSectionsComplex supportCComplex
  supportModelInclusion

set_option maxRecDepth 2048 in
/-- Derived global sections identify the entire specified support triangle with the
sectionwise supported triangle. The two chain isomorphisms are normalized by inclusion
and restriction; on injectives these determine them uniquely.
Source: Stacks Tag 09XP and Tag 014Z, cone-to-quotient construction
(blueprint: lem-pur-proetale-support-global-boundary).

Proof, following the node's steps 1--5: the supported-kernel comparison and support
exactness give the sheaf row with its actual kernel inclusion. The exact left adjoints
show that its three models are bounded below injective models. Restriction of an
injective module sheaf along the open monomorphism is surjective on sections by the
ringed-site restriction lemma, so the section row is short exact. Sections preserve the
supported kernel, giving a, and the direct-image section formula gives b. The cone has
injective terms since a finite sum of injectives is injective. Therefore the derived
units compute sections on the three models and on the cone. Sections carry its
signed differential matrix, inclusion and negative projection to the identical matrix
and maps of the section cone. Naturality of the unit at the cone quotient identifies
its image with the section quotient. Invert these quasi-isomorphisms. This gives the
triangle isomorphism with precisely the three displayed unit-normalized components,
including the shift comparison in the third-arrow square. -/
theorem supportGlobalTriangleComparison
    (I : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] :
    ∃ (hR : (supportGlobalRow A j I).ShortExact)
      (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient A i j hPair I.obj)))
      (hqR : IsIso (DerivedCategory.Q.map
        (CochainComplex.mappingCone.descShortComplex (supportGlobalRow A j I))))
      (a : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).obj (supportedSectionsComplex A i j hPair I.obj)) ≅
          (supportGlobalRow A j I).X₁)
      (b : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).obj (supportCComplex A j I.obj)) ≅ (supportGlobalRow A j I).X₃),
      a.hom ≫ (supportGlobalRow A j I).f =
        ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
          (.up ℤ)).map (supportModelSequence A i j hPair I.obj).f ∧
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
          (.up ℤ)).map (supportModelSequence A i j hPair I.obj).g ≫ b.hom =
        (supportGlobalRow A j I).g ∧
      ∃ e : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).rightDerivedFunctor
          ).mapTriangle.obj (supportModelTriangle A i j hPair I.obj hq)) ≅
            supportSequenceTriangle (supportGlobalRow A j I) hqR,
        e.hom.hom₁ =
          (supportGlobalUnitIso A (supportedSectionsComplex A i j hPair I.obj)
            (supportGlobalModels_kInjective A i j hPair I).2.1).hom ≫
              DerivedCategory.Q.map a.hom ∧
        e.hom.hom₂ = (supportGlobalUnitIso A I.obj
          (supportGlobalModels_kInjective A i j hPair I).1).hom ∧
        e.hom.hom₃ = (supportGlobalUnitIso A (supportCComplex A j I.obj)
          (supportGlobalModels_kInjective A i j hPair I).2.2).hom ≫
            DerivedCategory.Q.map b.hom ∧
        ∀ q : ℤ,
          DerivedCategory.HomologySequence.δ
              (supportSequenceTriangle (supportGlobalRow A j I) hqR) q (q + 1) rfl =
            (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A) q).hom.app
                (supportGlobalRow A j I).X₃ ≫
              hR.δ q (q + 1) rfl ≫
              (DerivedCategory.homologyFunctorFactors (ModuleCat.{u + 1} A)
                (q + 1)).inv.app (supportGlobalRow A j I).X₁ := by
  let F := supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))
  let E := F.mapHomologicalComplex (.up ℤ)
  let S := supportModelSequence A i j hPair I.obj
  let R := supportGlobalRow A j I
  have hk := supportGlobalModels_kInjective A i j hPair I
  have : I.obj.IsKInjective := hk.1
  have : S.X₁.IsKInjective := hk.2.1
  have : S.X₂.IsKInjective := hk.1
  have : S.X₃.IsKInjective := hk.2.2
  have (n : ℤ) : Injective (S.X₁.X n) := globalSupportTerms A i j hPair I n
  have hS : S.ShortExact :=
    (supportInjectiveConeDistinguished A i j hPair I.obj ⟨I.property, inferInstance⟩).1
  have hR := globalRow_shortExact A j I
  have hSE := globalMappedShortExact F hS
  let b : E.obj S.X₃ ≅ R.X₃ := by
    dsimp only [E, S, supportModelSequence, R, supportGlobalRow,
      Functor.injectiveBoundaryRow]
    unfold supportCComplex
    dsimp only [F]
    exact (Functor.mapHomologicalComplexCompIso (globalOpenEvaluationIso A j) (.up ℤ)).app
      I.obj
  have hb : E.map S.g ≫ b.hom = R.g := by
    ext n : 1
    dsimp only [E, S, supportModelSequence, b, R, supportGlobalRow,
      Functor.injectiveBoundaryRow]
    exact globalOpenSectionIso_unit A j (I.obj.X n)
  let e : S.map E ≅ R := shortComplexIsoFromQuotient hSE hR (Iso.refl _) b (by
    change 𝟙 _ ≫ R.g = E.map S.g ≫ b.hom
    simpa only [Category.id_comp] using hb.symm)
  have he₂ : e.hom.τ₂ = 𝟙 _ := shortComplexIsoFromQuotient_hom₂ _ _ _ _ _
  have he₃ : e.hom.τ₃ = b.hom := shortComplexIsoFromQuotient_hom₃ _ _ _ _ _
  let a : E.obj S.X₁ ≅ R.X₁ := ShortComplex.π₁.mapIso e
  have ha : a.hom ≫ R.f = E.map S.f := by
    have h := e.hom.comm₁₂
    change a.hom ≫ R.f = E.map S.f ≫ e.hom.τ₂ at h
    rw [he₂] at h
    exact h.trans (Category.comp_id _)
  have hq : IsIso (DerivedCategory.Q.map (supportConeQuotient A i j hPair I.obj)) := by
    change IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S))
    have := CochainComplex.mappingCone.quasiIso_descShortComplex hS
    infer_instance
  have hqR : IsIso (DerivedCategory.Q.map
      (CochainComplex.mappingCone.descShortComplex R)) := by
    have := CochainComplex.mappingCone.quasiIso_descShortComplex hR
    infer_instance
  let t := globalSequenceTriangleIso F hS hR hq hqR e
  refine ⟨hR, hq, hqR, a, b, ha, hb, t, ?_, ?_, ?_, ?_⟩
  · dsimp only [supportGlobalUnitIso, a, asIso_hom]
    exact globalSequenceTriangleIso_hom₁ F hS hR hq hqR e
  · have h := globalSequenceTriangleIso_hom₂ F hS hR hq hqR e
    rw [he₂] at h
    erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h
  · have h := globalSequenceTriangleIso_hom₃ F hS hR hq hqR e
    rw [he₃] at h
    exact h
  · exact sequenceIntegerBoundary R hR hqR

end TriangleComparison

/-- Naturality of the normalized sectionwise identifications in chain maps of
injective representatives. Together with the natural derived units and the K-injective
Hom bijection, these are the naturality squares for every derived morphism in K.
Source: Stacks Tags 09XP, 014Z and 070I
(blueprint: lem-pur-proetale-support-global-boundary).
Proof: compose the first proposed equality with the monic support inclusion. The two
results agree by naturality of the actual supported inclusion. For the second square,
precompose with the degreewise epic restriction map out of I; both composites are
restriction followed by the given chain map. Cancel that epimorphism. The cone map is
(fb,fa) and commutes with quotient and negative projection. Derived units are natural,
and the K-injective Hom bijection represents every derived map by a chain map modulo
homotopy. All functors preserve homotopies, so the squares descend independently of
the representative and also compare distinct resolutions of one K. -/
theorem supportGlobalComparisonNatural
    (I J : CochainComplex.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    [∀ n : ℤ, Injective (I.obj.X n)] [∀ n : ℤ, Injective (J.obj.X n)] (f : I ⟶ J)
    (aI : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportedSectionsComplex A i j hPair I.obj)) ≅
        (supportGlobalRow A j I).X₁)
    (aJ : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportedSectionsComplex A i j hPair J.obj)) ≅
        (supportGlobalRow A j J).X₁)
    (bI : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportCComplex A j I.obj)) ≅ (supportGlobalRow A j I).X₃)
    (bJ : (((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
      (.up ℤ)).obj (supportCComplex A j J.obj)) ≅ (supportGlobalRow A j J).X₃)
    (_haI : aI.hom ≫ (supportGlobalRow A j I).f =
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair I.obj).f)
    (_haJ : aJ.hom ≫ (supportGlobalRow A j J).f =
      ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair J.obj).f)
    (_hbI : ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair I.obj).g ≫ bI.hom =
          (supportGlobalRow A j I).g)
    (_hbJ : ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportModelSequence A i j hPair J.obj).g ≫ bJ.hom =
          (supportGlobalRow A j J).g) :
    ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportAMap A i j hPair f.hom) ≫ aJ.hom =
      aI.hom ≫ ((Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A) (supportGlobalRestriction j)).mapHomologicalComplex
          (.up ℤ)).map f.hom ∧
    ((supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
        (.up ℤ)).map (supportCMap A j f.hom) ≫ bJ.hom =
      bI.hom ≫ ((supportGlobalEvaluation A (Scheme.ProEt.mk j)).mapHomologicalComplex
        (.up ℤ)).map f.hom := by
  let E := (supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))).mapHomologicalComplex
    (.up ℤ)
  have hA : supportAMap A i j hPair f.hom ≫ (supportModelSequence A i j hPair J.obj).f =
      (supportModelSequence A i j hPair I.obj).f ≫ f.hom := by
    ext n : 1
    exact (supportModelInclusion A i j hPair).naturality (f.hom.f n)
  have hC : (supportModelSequence A i j hPair I.obj).g ≫ supportCMap A j f.hom =
      f.hom ≫ (supportModelSequence A i j hPair J.obj).g := by
    ext n : 1
    exact ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) j).unit.naturality
      (f.hom.f n)).symm
  have hm : Mono (supportGlobalRow A j J).f := (globalRow_shortExact A j J).mono_f
  have he : Epi (supportGlobalRow A j I).g := (globalRow_shortExact A j I).epi_g
  have he' : Epi (E.map (supportModelSequence A i j hPair I.obj).g) := by
    apply (epi_comp_iff_of_isIso _ bI.hom).mp
    rw [_hbI]
    infer_instance
  constructor
  · apply (cancel_mono (supportGlobalRow A j J).f).1
    change (E.map _ ≫ aJ.hom) ≫ _ = (aI.hom ≫ _) ≫ _
    rw [Category.assoc, _haJ, ← E.map_comp, hA, E.map_comp, ← _haI,
      Category.assoc, Category.assoc]
    congr 1
    exact ((NatTrans.mapHomologicalComplex
      (Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A) (supportGlobalRestriction j)) (.up ℤ)).naturality f.hom).symm
  · apply (cancel_epi (E.map (supportModelSequence A i j hPair I.obj).g)).1
    change E.map _ ≫ (E.map _ ≫ bJ.hom) = E.map _ ≫ (bI.hom ≫ _)
    rw [← Category.assoc, ← E.map_comp, hC, E.map_comp, Category.assoc,
      _hbJ, ← Category.assoc, _hbI]
    exact ((NatTrans.mapHomologicalComplex
      ((sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
        (supportGlobalRestriction j).op) (.up ℤ)).naturality f.hom)

include hA hi hqc hPair in
set_option linter.unusedSectionVars false in
/-- The supported cohomology boundary is the global triangle boundary, with the
positive differential-of-a-lift formula in every integer degree, naturally in K.
Source: Stacks Tag 09XP and Tag 014Z
(blueprint: lem-pur-proetale-support-global-boundary).

Proof, following steps 6--8: for a cocycle c choose a lift b by sectionwise
surjectivity. There is a unique a in the support kernel with u(a)=db. Its differential
vanishes since u is monic and d²=0. The section cone cocycle (b,-a) maps to c under
the cone quotient, and the third arrow -projection maps it to a. Thus the triangle
boundary is the snake boundary and sends [c] to [db], with no extra sign. Changing
the lift adds a boundary; changing the cocycle by a boundary does not change its
image. The derived-injective-boundary normalization identifies this with the natural
supported-cohomology boundary of the support long exact sequence. A chain map sends
(b,-a) to (fb,-fa) and commutes with the quotient and projection, so all comparisons
commute with chain maps. Every derived map into a bounded below injective complex is
represented by a chain map uniquely up to homotopy. Additive functors preserve these
homotopies; hence the normalization and identifications are natural for all derived
morphisms and independent of the chosen injective resolution. -/
theorem supportGlobalBoundaryNormalization :
    ∃ δ : Sheaf.SupportSequenceBoundary (Scheme.ProEt.topology X)
        (ModuleCat.{u + 1} A) (supportGlobalRestriction j) ⊤,
      Sheaf.SupportSequenceExact (Scheme.ProEt.topology X)
          (ModuleCat.{u + 1} A) (supportGlobalRestriction j) ⊤ δ ∧
      ∀ (I : CochainComplex.Plus
        (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
        [∀ n : ℤ, Injective (I.obj.X n)],
        ∃ hR : (supportGlobalRow A j I).ShortExact,
          (∀ (K : DerivedCategory.Plus
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
            (e : DerivedCategory.Plus.Q.obj I ≅ K) (q : ℤ),
            (Sheaf.supportSequenceModelIso _ _
              (supportGlobalEvaluation A (Scheme.ProEt.mk j)) I K e q).hom ≫
                (δ q).app ⟨K, trivial⟩ ≫
                (Sheaf.supportSequenceModelIso _ _
                  (Sheaf.supportedSectionsFunctor _ _ (supportGlobalRestriction j))
                  I K e (q + 1)).inv = hR.δ q (q + 1) rfl) ∧
          (∀ (q : ℤ) (c : (supportGlobalRow A j I).X₃.X q)
            (hc : (supportGlobalRow A j I).X₃.d q (q + 1) c = 0)
            (b : (supportGlobalRow A j I).X₂.X q)
            (_hb : (supportGlobalRow A j I).g.f q b = c),
            ∃ (a : (supportGlobalRow A j I).X₁.X (q + 1))
              (ha : (supportGlobalRow A j I).X₁.d (q + 1) (q + 1 + 1) a = 0),
              (supportGlobalRow A j I).f.f (q + 1) a =
                (supportGlobalRow A j I).X₂.d q (q + 1) b ∧
              hR.δ q (q + 1) rfl
                ((supportGlobalRow A j I).X₃.homologyπ q
                  ((supportGlobalRow A j I).X₃.cyclesMk c (q + 1) (by simp) hc)) =
                (supportGlobalRow A j I).X₁.homologyπ (q + 1)
                  ((supportGlobalRow A j I).X₁.cyclesMk a (q + 1 + 1) (by simp) ha)) := by
  classical
  let S := Sheaf.supportedSectionsFunctor (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} A) (supportGlobalRestriction j)
  let F := supportGlobalEvaluation A (Scheme.ProEt.mk (𝟙 X))
  let G := supportGlobalEvaluation A (Scheme.ProEt.mk j)
  let ι := Sheaf.supportedSectionsInclusion (Scheme.ProEt.topology X)
    (ModuleCat.{u + 1} A) (supportGlobalRestriction j)
  let π := (sheafSections (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)).map
    (supportGlobalRestriction j).op
  obtain ⟨δ, hδ⟩ := Functor.exists_injectiveBoundary S F G ι π
    (supportGlobalRestriction_zero A j) (globalRow_termwise A j)
  refine ⟨fun q ↦ Functor.whiskerLeft (⊤ : ObjectProperty _).ι (δ q), ?_, ?_⟩
  · intro K q
    let Q := (InjectiveObject.ι
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))).mapHomotopyCategoryPlus ⋙
        DerivedCategory.Plus.Qh
    let M := Q.objPreimage K.obj
    obtain ⟨L, hL⟩ := HomotopyCategory.Plus.quotient_obj_surjective M
    let I := (InjectiveObject.ι _).mapCochainComplexPlus.obj L
    have (n : ℤ) : Injective (I.obj.X n) :=
      inferInstanceAs (Injective (L.obj.X n).obj)
    let e : DerivedCategory.Plus.Q.obj I ≅ K.obj :=
      Q.mapIso (eqToIso hL) ≪≫ Q.objObjPreimageIso K.obj
    exact Functor.injectiveBoundary_exact S F G ι π
      (supportGlobalRestriction_zero A j) (globalRow_termwise A j) δ hδ I K.obj e q
  · intro I _
    let R := supportGlobalRow A j I
    let hR := globalRow_shortExact A j I
    refine ⟨hR, ?_, ?_⟩
    · intro K e q
      exact hδ I K e q
    · intro q c hc b hb
      dsimp only [R, supportGlobalRow, Functor.injectiveBoundaryRow] at *
      exact globalCocycleFormula _ hR q c hc b hb

end AlgebraicGeometry.ProEtale
