/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemSingletonSequenceTranspose
public import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategorySquareIsoFactors

/-! # Normalized representative of singleton coefficient change

## Implementation details

Both composite derived adjunctions are normalized on representatives: the singleton
adjunction by `singletonSequenceDerivedAdjunction_homEquiv` and the scalar adjunctions by
their recorded transposes. Adjoint uniqueness then identifies the derived conjugate with the
localized ordinary conjugate, as for the scalar associator.

## References

* Stacks Project, Tags 09T5, 0D6D, 0FND
* Zheng, Construction 4.1
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]

variable (S : SystemScalarAssignment (J := J)) (T : SystemTensorCoherence S)
  {B D : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}} (a : B ⟶ D)
  (A : SystemScalarModel (singletonSequenceRingMap a))

/-- The specified derived conjugate is represented by the ordinary singleton
coefficient comparison, with the actual universal comparison maps. -/
theorem singletonScalarDerivedIso_rep (n : ℕ)
    (P : CochainComplex (systemLevel B n) ℤ) :
      (singletonScalarDerivedIso S T a A n).hom.app (DerivedCategory.Q.obj P) ≫
          singletonScalarTargetComparison S T a n P =
        singletonScalarSourceComparison S T a A n P ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (singletonScalarOrdinaryIso S T a A n)
            (.up ℤ)).hom.app P) := by
  let Rs := singletonSequenceRestriction a
  let Rl := singletonLevelRestriction a n
  let eB := systemSequenceEvaluation B n
  let eD := systemSequenceEvaluation D n
  let η₀ := singletonRestrictionEvaluation a n
  let δ := singletonDerivedRestrictionEvaluation a n
  let ν := singletonScalarOrdinaryIso S T a A n
  let Sa := S (a.app (op n))
  let ac := (singletonSequenceOrdinaryAdjunction S T B n).mapHomologicalComplex (.up ℤ)
  let bc := A.ordinaryAdj.mapHomologicalComplex (.up ℤ)
  let cc := Sa.ordinaryAdj.mapHomologicalComplex (.up ℤ)
  let dc := (singletonSequenceOrdinaryAdjunction S T D n).mapHomologicalComplex (.up ℤ)
  let ηc : Rs.mapHomologicalComplex (.up ℤ) ⋙ eB.mapHomologicalComplex (.up ℤ) ≅
      eD.mapHomologicalComplex (.up ℤ) ⋙ Rl.mapHomologicalComplex (.up ℤ) :=
    Functor.mapHomologicalComplexCompIso η₀ (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl (eD ⋙ Rl)) (.up ℤ)).symm
  let νc := Functor.mapHomologicalComplexCompIso ν (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) (.up ℤ)).symm
  have hn : ∀ P, (ac.comp bc).homEquiv _ _ (νc.hom.app P) ≫
      ηc.hom.app (((Sa.model.E ⋙ singletonSequenceOrdinary S T D n).mapHomologicalComplex
        (.up ℤ)).obj P) = (cc.comp dc).unit.app P := by
    intro P
    apply HomologicalComplex.hom_ext
    intro i
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (((singletonSequenceOrdinaryAdjunction S T B n).comp A.ordinaryAdj).ofNatIsoRight η₀)
      (Sa.ordinaryAdj.comp (singletonSequenceOrdinaryAdjunction S T D n)) (P.X i)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at h
    rw [Adjunction.homEquiv_unit]
    simp only [ac, bc, cc, dc, νc, ηc, ν, Adjunction.comp_unit_app] at h ⊢
    simp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Functor.comp_map, Functor.map_comp, Category.assoc,
      HomologicalComplex.comp_f, Adjunction.mapHomologicalComplex_unit_app_f,
      Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
      CategoryTheory.Functor.map_id, Category.id_comp] at h ⊢
    erw [Category.comp_id]
    exact h
  have hρ : ∀ K, ((eB.mapDerivedCategoryFactors.inv.app
      (Rs.mapHomologicalComplex (.up ℤ) |>.obj K) ≫
        eB.mapDerivedCategory.map (Rs.mapDerivedCategoryFactors.inv.app K)) ≫
        δ.hom.app (DerivedCategory.Q.obj K)) =
      DerivedCategory.Q.map (ηc.hom.app K) ≫
        (Rl.mapDerivedCategoryFactors.inv.app (eD.mapHomologicalComplex (.up ℤ) |>.obj K) ≫
          Rl.mapDerivedCategory.map (eD.mapDerivedCategoryFactors.inv.app K)) := by
    intro K
    have hs := Functor.mapDerivedCategorySquareIso_hom_app_factors _ _ _ _ η₀ K
    rw [← cancel_mono (Rl.mapDerivedCategory.map (eD.mapDerivedCategoryFactors.hom.app K) ≫
      Rl.mapDerivedCategoryFactors.hom.app (eD.mapHomologicalComplex (.up ℤ) |>.obj K))]
    simp only [Category.assoc]
    erw [hs]
    simp only [Rs, eB, Rl, eD]
    rw [← Functor.map_comp_assoc (systemSequenceEvaluation B n).mapDerivedCategory,
      Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id (systemSequenceEvaluation B n).mapDerivedCategory]
    rw [Category.id_comp, Iso.inv_hom_id_app_assoc]
    rw [← Functor.map_comp_assoc (singletonLevelRestriction a n).mapDerivedCategory,
      Iso.inv_hom_id_app]
    erw [CategoryTheory.Functor.map_id (singletonLevelRestriction a n).mapDerivedCategory]
    rw [Category.id_comp, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    congr 1
  let εB : DerivedCategory.Q ⋙ singletonSequenceDerived S T B n ⟶
      (singletonSequenceOrdinary S T B n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (systemSingleDerivedExtension B n S T).comparison
        (strictSystemSequenceEquivalence B).functor.mapDerivedCategory ≫
      Functor.whiskerLeft ((systemSingleFunctor S T B n).mapHomologicalComplex (.up ℤ))
        (strictSystemSequenceEquivalence B).functor.mapDerivedCategoryFactors.hom
  let εD : DerivedCategory.Q ⋙ singletonSequenceDerived S T D n ⟶
      (singletonSequenceOrdinary S T D n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (systemSingleDerivedExtension D n S T).comparison
        (strictSystemSequenceEquivalence D).functor.mapDerivedCategory ≫
      Functor.whiskerLeft ((systemSingleFunctor S T D n).mapHomologicalComplex (.up ℤ))
        (strictSystemSequenceEquivalence D).functor.mapDerivedCategoryFactors.hom
  have hF := normalizedAdjunction_composition ac bc (singletonSequenceDerivedAdjunction S T B n)
    A.adjunction εB A.model.ε eB.mapDerivedCategoryFactors.inv Rs.mapDerivedCategoryFactors.inv
    (singletonSequenceDerivedAdjunction_homEquiv S T B n) A.transpose
  have hH := normalizedAdjunction_composition cc dc Sa.adjunction
    (singletonSequenceDerivedAdjunction S T D n) Sa.model.ε εD
    Rl.mapDerivedCategoryFactors.inv eD.mapDerivedCategoryFactors.inv
    Sa.transpose (singletonSequenceDerivedAdjunction_homEquiv S T D n)
  have h := normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q) (ac.comp bc) (cc.comp dc)
    ((singletonSequenceDerivedAdjunction S T B n).comp A.adjunction)
    (Sa.adjunction.comp (singletonSequenceDerivedAdjunction S T D n))
    (singletonScalarSourceComparison S T a A n) (singletonScalarTargetComparison S T a n)
    (fun K ↦ eB.mapDerivedCategoryFactors.inv.app
        (Rs.mapHomologicalComplex (.up ℤ) |>.obj K) ≫
      eB.mapDerivedCategory.map (Rs.mapDerivedCategoryFactors.inv.app K))
    (fun K ↦ Rl.mapDerivedCategoryFactors.inv.app
        (eD.mapHomologicalComplex (.up ℤ) |>.obj K) ≫
      Rl.mapDerivedCategory.map (eD.mapDerivedCategoryFactors.inv.app K))
    (fun P K f ↦ by
      rw [singletonScalarSourceComparison, Category.assoc]; exact hF P K f)
    (fun P K f ↦ by
      rw [singletonScalarTargetComparison, Category.assoc]; exact hH P K f)
    ηc δ νc.hom.app hn hρ P
  have hv : νc.hom.app P = (NatIso.mapHomologicalComplex ν (.up ℤ)).hom.app P := by
    apply HomologicalComplex.hom_ext
    intro i
    simp [νc]
  rw [hv] at h
  exact h
end SheafOfModules
