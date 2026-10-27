/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C6
-/
module

public import Sheaf.Paper.IntegralComparisonCanonicalShifts
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Shift compatibility of scalar/pullback interchange on strict systems
Source: Stacks Tags 014E, 06YY and 0D6D.
(blueprint: lem-sf-integral-sequence-scalar-pullback-shifts). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

private theorem shift_of_dense_computation
    {A B C : Type*} [Category A] [Category B] [Category C]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ] (G H : B ⥤ C)
    [G.CommShift ℤ] [H.CommShift ℤ] (F : A ⥤ C) [F.CommShift ℤ]
    (α : Q ⋙ H ⟶ F) (β : Q ⋙ G ⟶ F)
    [NatTrans.CommShift α ℤ] [NatTrans.CommShift β ℤ]
    (t : G ⟶ H) (good : A → Prop)
    (stable : ∀ X, good X → ∀ n : ℤ, good (X⟦n⟧))
    (computation : ∀ X, good X → t.app (Q.obj X) ≫ α.app X = β.app X)
    (dense : ∀ Y : B, ∃ (X : A) (_e : Q.obj X ≅ Y), good X ∧ IsIso (α.app X)) :
    NatTrans.CommShift t ℤ := by
  constructor
  intro n
  let s : shiftFunctor B n ⋙ G ⟶ H ⋙ shiftFunctor C n :=
    (G.commShiftIso n).hom ≫ Functor.whiskerRight t (shiftFunctor C n)
  let u : shiftFunctor B n ⋙ G ⟶ H ⋙ shiftFunctor C n :=
    Functor.whiskerLeft (shiftFunctor B n) t ≫ (H.commShiftIso n).hom
  have onGood (X : A) (hX : good X) [IsIso (α.app X)] :
      s.app (Q.obj X) = u.app (Q.obj X) := by
    apply (cancel_mono ((shiftFunctor C n).mapIso (asIso (α.app X))).hom).1
    change s.app (Q.obj X) ≫ (α.app X)⟦n⟧' =
      u.app (Q.obj X) ≫ (α.app X)⟦n⟧'
    apply (cancel_epi (G.mapIso ((Q.commShiftIso n).app X)).hom).1
    change G.map ((Q.commShiftIso n).hom.app X) ≫ s.app (Q.obj X) ≫
      (α.app X)⟦n⟧' = G.map ((Q.commShiftIso n).hom.app X) ≫ u.app (Q.obj X) ≫
      (α.app X)⟦n⟧' 
    have ht := NatTrans.shift_app_comm β n X
    rw [← computation X hX, ← computation (X⟦n⟧) (stable X hX n)] at ht
    have ha := NatTrans.shift_app_comm α n X
    simp only [Functor.commShiftIso_comp_hom_app, Functor.map_comp,
      Category.assoc] at ht ha
    rw [← ha, ← t.naturality_assoc] at ht
    simpa only [s, u, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.assoc] using ht
  ext Y
  obtain ⟨X, e, hX, hi⟩ := dense Y
  let := hi
  have h := congrArg (fun f ↦ f ≫ (H ⋙ shiftFunctor C n).map e.hom) (onGood X hX)
  rw [← s.naturality, ← u.naturality] at h
  exact (cancel_epi (((shiftFunctor B n) ⋙ G).mapIso e).hom).1 h

private theorem complexComp_commShift
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Preadditive A] [Preadditive B] [Preadditive C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    [F.Additive] [G.Additive] [H.Additive] (e : F ⋙ G ≅ H) :
    NatTrans.CommShift (Functor.mapHomologicalComplexCompIso e (.up ℤ)).hom ℤ := by
  constructor
  intro n
  ext K i
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.commShiftIso_comp_hom_app, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]
  rfl

/-- The independently counit-normalized scalar shifts commute with the fixed
whole-system scalar/pullback comparison.

Source: Stacks Tags 014E, 06YY and 0D6D; the scalar/pullback comparison step of
the open-closed triangle proof.
(blueprint: lem-sf-integral-sequence-scalar-pullback-shifts).

Proof: form the two cochain computation transformations to the localization
of the ordinary composite scalar and pullback functors. They use the universal
scalar counits, the exact pullback localization comparisons, and the ordinary
scalar/pullback associator. Each of these transformations commutes with shifts:
the scalar counits by their universal normalization, the pullback comparisons
by the exact termwise normalization, and the ordinary associator degreewise
since its balanced maps have degree zero. On a K-flat P the normalization in
integralComparisonSystemScalarPullback_existsUnique identifies the two
computations after the derived associator. The target computation is invertible
there, and P[m] is K-flat too. Compare the computation squares at P and P[m]
and cancel the target computation to obtain the associator square on Q(P).
Resolve an arbitrary complex by a flat-term K-flat P; naturality transports
this square along its localized quasi-isomorphism. Essential surjectivity
of localization then proves the natural-transformation shift equation. -/
theorem integralComparisonSystemScalarPullback_commShift
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    letI := integralComparisonSequencePullbackShift l E f
    letI := integralComparisonSequencePullbackShift l L f
    letI := integralComparisonSequenceScalarShift l E L ι X
    letI := integralComparisonSequenceScalarShift l E L ι Y
    NatTrans.CommShift (integralComparisonSystemScalarPullback l E L ι f).hom ℤ := by
  let := integralComparisonSequencePullbackShift l E f
  let := integralComparisonSequencePullbackShift l L f
  let := integralComparisonSequenceScalarShift l E L ι X
  let := integralComparisonSequenceScalarShift l E L ι Y
  let MX := integralComparisonSequenceScalarModel l E L ι X
  let MY := integralComparisonSequenceScalarModel l E L ι Y
  let PE := integralComparisonSequencePullback l E f
  let PL := integralComparisonSequencePullback l L f
  let : MX.T.CommShift ℤ := integralComparisonSequenceScalarShift l E L ι X
  let : MY.T.CommShift ℤ := integralComparisonSequenceScalarShift l E L ι Y
  let : NatTrans.CommShift MX.ε ℤ :=
    (integralComparisonSequenceScalarShift_exists l E L ι X).choose_spec
  let : NatTrans.CommShift MY.ε ℤ :=
    (integralComparisonSequenceScalarShift_exists l E L ι Y).choose_spec
  let a := integralComparisonSequenceScalarPullback l E L ι f
  let k := Functor.mapHomologicalComplexCompIso a (.up ℤ) ≪≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (MY.E ⋙ PL)) (.up ℤ)).symm
  have : NatTrans.CommShift k.hom ℤ := by
    let := complexComp_commShift a
    let := complexComp_commShift (Iso.refl (MY.E ⋙ PL))
    dsimp [k]
    infer_instance
  let α := (Functor.associator DerivedCategory.Q MY.T
      (integralComparisonDerivedSequencePullback l L f)).inv ≫
    Functor.whiskerRight MY.ε (integralComparisonDerivedSequencePullback l L f) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (MY.E.mapHomologicalComplex (.up ℤ))
      PL.mapDerivedCategoryFactors.hom
  let β := (Functor.associator DerivedCategory.Q
      (integralComparisonDerivedSequencePullback l E f) MX.T).inv ≫
    Functor.whiskerRight PE.mapDerivedCategoryFactors.hom MX.T ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (PE.mapHomologicalComplex (.up ℤ)) MX.ε ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight k.hom DerivedCategory.Q ≫
    (Functor.associator _ _ _).hom
  have : NatTrans.CommShift α ℤ := by dsimp [α]; infer_instance
  have : NatTrans.CommShift β ℤ := by dsimp [β]; infer_instance
  let t := (integralComparisonSystemScalarPullback l E L ι f).hom
  apply shift_of_dense_computation DerivedCategory.Q _ _ _ α β t
    (fun P ↦ CochainComplex.IsKFlatIndependentCoefficients
      (R := coefficientSequenceCommRingSheaf l E Y) P)
  · intro P hP n
    let R := coefficientSequenceCommRingSheaf l E Y
    let := SheafOfModules.isMonoidal_W_independentCoefficients R
    let := SheafOfModules.monoidalCategory R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
    have (M : coefficientSequenceModules l E Y) :
        (MonoidalCategory.tensorLeft M).Additive :=
      SheafOfModules.tensorLeft_additive_independent R M
    intro F hF
    have ht := hP F hF
    have hs : (CochainComplex.mapBifunctor F P
        (MonoidalCategory.curriedTensor _)⟦n⟧).Acyclic := by
      rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at ht ⊢
      rw [← HomotopyCategory.shift_quotient_obj]
      exact (HomotopyCategory.subcategoryAcyclic _).le_shift n _ ht
    intro i
    exact (hs i).of_iso
      (CochainComplex.mapBifunctorShift₂Iso F P (MonoidalCategory.curriedTensor _) n).symm
  · intro P hP
    have h := (integralComparisonSystemScalarPullback_existsUnique l E L ι f).exists.choose_spec
      P hP
    simpa [α, β, t, MX, MY, PE, PL, k, a, integralComparisonSystemScalarPullback,
      Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      integralComparisonDerivedSequenceScalar, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
      Functor.associator_hom_app, Category.id_comp, Category.comp_id,
      Category.assoc] using h.symm
  · intro N
    let P₀ := DerivedCategory.Q.objPreimage N
    obtain ⟨P, r, hP, hf, hq, hr⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients P₀
    let : IsIso (DerivedCategory.Q.map r) :=
      Localization.inverts DerivedCategory.Q (HomologicalComplex.quasiIso _ _) r hq
    refine ⟨P, asIso (DerivedCategory.Q.map r) ≪≫
      DerivedCategory.Q.objObjPreimageIso N, hP, ?_⟩
    let := MY.computes P hP
    dsimp [α]
    infer_instance

end WeilConjectures
