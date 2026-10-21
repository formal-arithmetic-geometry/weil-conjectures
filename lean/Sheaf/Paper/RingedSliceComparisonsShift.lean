/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.Paper.RingedDerivedSliceLocalization
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import Sheaf.CategoryTheory.DerivedCategory.DerivedSquareShiftOnKInjectives
import Sheaf.CategoryTheory.AdjunctionSquareShiftMate
import Sheaf.Algebra.Homology.SliceTensorIntegerShiftCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift

/-! # Integer shifts of canonical ringed-slice comparisons

Source: Stacks Project, sites-cohomology.tex, Tags 08FI and 07A4, and the
agent-written signed-shift calculation from these constructions
(blueprint: lem-weil-pbc-ringed-slice-comparisons-shift).

The helper predicates only spell out the representative normalization and the four
squares in this statement. Tensor, restriction, and the derived adjunctions are the
existing constructions. No comparison is selected from an arbitrary existence claim.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures MonoidalCategory

namespace SheafOfModules

-- The normalized-unit argument of DerivedAdjunctionShift, on complexes.
private theorem rightKan_postadjoint_ext
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Q : A ⥤ B) (F : A ⥤ C) (LF : B ⥤ C) (α : Q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] (T : D ⥤ C) (S : C ⥤ D) (a : T ⊣ S)
    (H : B ⥤ D) (γ₁ γ₂ : H ⟶ LF ⋙ S)
    (h : ∀ X, γ₁.app (Q.obj X) ≫ S.map (α.app X) =
      γ₂.app (Q.obj X) ≫ S.map (α.app X)) : γ₁ = γ₂ := by
  apply ((a.whiskerRight B).homEquiv H LF).symm.injective
  apply LF.hom_ext_of_isRightKanExtension α
  simp only [Adjunction.homEquiv_counit]
  ext X
  have hx := congrArg ((a.homEquiv (H.obj (Q.obj X)) (F.obj X)).symm) (h X)
  simpa [Adjunction.homEquiv_counit, CategoryTheory.Functor.map_comp, Category.assoc,
    ← a.counit.naturality, Adjunction.whiskerRight_counit_app_app] using hx

private theorem rightKan_postadjoint_commShift
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (Q : A ⥤ B) [Q.CommShift ℤ] (F : A ⥤ C) [F.CommShift ℤ]
    (LF : B ⥤ C) [LF.CommShift ℤ] (α : Q ⋙ LF ⟶ F)
    [LF.IsRightKanExtension α] [NatTrans.CommShift α ℤ]
    (T : D ⥤ C) (S : C ⥤ D) [S.CommShift ℤ] (a : T ⊣ S)
    (H : B ⥤ D) [H.CommShift ℤ] (τ : H ⟶ LF ⋙ S)
    [NatTrans.CommShift (Functor.whiskerLeft Q τ ≫
      (Functor.associator Q LF S).inv ≫ Functor.whiskerRight α S) ℤ] :
    NatTrans.CommShift τ ℤ := by
  let δ := (Functor.associator Q LF S).inv ≫ Functor.whiskerRight α S
  have : NatTrans.CommShift δ ℤ := by dsimp [δ]; infer_instance
  have hτ : NatTrans.CommShift (Functor.whiskerLeft Q τ ≫ δ) ℤ := by assumption
  constructor
  intro n
  apply rightKan_postadjoint_ext Q F LF α
    ((shiftEquiv D n).symm.functor ⋙ T) (S ⋙ shiftFunctor D n)
    ((shiftEquiv D n).symm.toAdjunction.comp a)
  intro X
  have hdapp (Y : A) : δ.app Y = S.map (α.app Y) := by
    simp [δ]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_map, ← hdapp X]
  apply (cancel_epi (H.map ((Q.commShiftIso n).hom.app X))).mp
  have hd := NatTrans.shift_app_comm δ n X
  have ht := NatTrans.shift_app_comm (Functor.whiskerLeft Q τ ≫ δ) n X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, CategoryTheory.Functor.map_comp,
    Category.assoc] at ht
  rw [← hd] at ht
  have hn := τ.naturality ((Q.commShiftIso n).hom.app X)
  dsimp at hn
  have hn' := congrArg (fun f ↦ f ≫ ((LF ⋙ S).commShiftIso n).hom.app (Q.obj X) ≫
    (shiftFunctor D n).map (δ.app X)) hn
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc, Functor.comp_map] at ht
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at hn' ⊢
  exact ht.trans hn'.symm

private theorem normalized_unit_commShift
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift C ℤ] [HasShift D ℤ]
    (QA : A ⥤ C) (QB : B ⥤ D) [QA.CommShift ℤ] [QB.CommShift ℤ]
    (F : A ⥤ B) (G : B ⥤ A) [F.CommShift ℤ] [G.CommShift ℤ]
    (L : C ⥤ D) (R : D ⥤ C) [L.CommShift ℤ] [R.CommShift ℤ]
    (ah : F ⊣ G) [NatTrans.CommShift ah.unit ℤ] (adj : L ⊣ R)
    (α : QA ⋙ L ⟶ F ⋙ QB) (β : G ⋙ QA ⟶ QB ⋙ R)
    [L.IsRightKanExtension α] [NatTrans.CommShift α ℤ] [NatTrans.CommShift β ℤ]
    (hnorm : ∀ (M : A) (N : B) (f : F.obj M ⟶ N),
      adj.homEquiv (QA.obj M) (QB.obj N) (α.app M ≫ QB.map f) =
        QA.map (ah.homEquiv M N f) ≫ β.app N) :
    NatTrans.CommShift adj.unit ℤ := by
  have hnorm' (M : A) : adj.unit.app (QA.obj M) ≫ R.map (α.app M) =
      QA.map (ah.unit.app M) ≫ β.app (F.obj M) := by
    have h := hnorm M _ (𝟙 _)
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit] at h
    simpa only [CategoryTheory.Functor.map_id, Functor.comp_obj, Functor.id_obj,
      Category.comp_id] using h
  let δ := Functor.whiskerLeft QA adj.unit ≫
    (Functor.associator QA L R).inv ≫ Functor.whiskerRight α R
  have heq : δ =
      (Functor.rightUnitor QA).hom ≫ (Functor.leftUnitor QA).inv ≫
      Functor.whiskerRight ah.unit QA ≫ (Functor.associator F G QA).hom ≫
      Functor.whiskerLeft F β ≫ (Functor.associator F QB R).inv := by
    ext M
    simpa [δ] using hnorm' M
  have hδ : NatTrans.CommShift δ ℤ := by
    rw [heq]
    infer_instance
  exact rightKan_postadjoint_commShift QA _ L α L R adj (𝟭 _) adj.unit

-- Conjugate a normalization without unfolding any of the functors involved.
private theorem iso_normalization_cancel
    {B C : Type*} [Category B] [Category C] (G : B ⥤ C)
    {X Y Z W : C} {P Q : B} (a : X ≅ Y) (b : P ≅ Q)
    (f₁ : X ⟶ Z) (f₂ : Z ⟶ G.obj P) (c : Y ⟶ W) (g : W ⟶ G.obj Q)
    (h : f₁ ≫ f₂ ≫ G.map b.hom = a.hom ≫ c ≫ g) :
    (a.inv ≫ f₁) ≫ f₂ = c ≫ (g ≫ G.map b.inv) := by
  have hh := congrArg (fun z ↦ a.inv ≫ z ≫ G.map b.inv) h
  simpa only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id, Iso.inv_hom_id_assoc] using hh

private theorem shift_mate_commShift
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (r : C ⥤ C') (t : D ⥤ D')
    [L.CommShift ℤ] [R.CommShift ℤ] [L'.CommShift ℤ] [R'.CommShift ℤ]
    [r.CommShift ℤ] [t.CommShift ℤ]
    [NatTrans.CommShift adj.unit ℤ] [NatTrans.CommShift adj'.unit ℤ]
    (β : R ⋙ r ⟶ t ⋙ R') [NatTrans.CommShift β ℤ]
    (θ : r ⋙ L' ⟶ L ⋙ t)
    (hθ : ∀ P, θ.app P = L'.map (r.map (adj.unit.app P) ≫ β.app (L.obj P)) ≫
      adj'.counit.app (t.obj (L.obj P))) : NatTrans.CommShift θ ℤ := by
  have hu (n : ℤ) : Adjunction.CommShift.CompatibilityUnit adj
      (L.commShiftIso n) (R.commShiftIso n) := by
    intro X
    simpa only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      Functor.comp_obj, Functor.id_obj, Category.id_comp] using
      (NatTrans.shift_app_comm adj.unit n X)
  have hu' (n : ℤ) : Adjunction.CommShift.CompatibilityUnit adj'
      (L'.commShiftIso n) (R'.commShiftIso n) := by
    intro X
    simpa only [Functor.commShiftIso_comp_hom_app, Functor.commShiftIso_id_hom_app,
      Functor.comp_obj, Functor.id_obj, Category.id_comp] using
      (NatTrans.shift_app_comm adj'.unit n X)
  constructor
  intro n
  ext P
  have h := (Adjunction.square_shift_mate adj adj' r t hu hu' β (fun E n ↦ by
    simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using
      (NatTrans.shift_app_comm β n E).symm) P n).2.2.2
  simpa only [← hθ, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app, Category.assoc] using h.symm

private def tensorShiftComparisons
    {D : Type*} [Category D] [Preadditive D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    (B : D × D ⥤ D) [(Functor.curry.obj B).CommShift₂Int] :
    TensorIntegerShiftComparisons B where
  first n := NatIso.ofComponents
    (fun X ↦ (((Functor.curry.obj B).flip.obj X.2).commShiftIso n).app X.1) (by
      rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
      have h₁ := NatTrans.shift_app_comm ((Functor.curry.obj B).flip.map g) n X'
      have h₂ := (((Functor.curry.obj B).flip.obj Y).commShiftIso n).hom.naturality f
      dsimp at h₁ h₂ ⊢
      rw [show B.map (Prod.mkHom (f⟦n⟧') g) =
        B.map (Prod.mkHom (f⟦n⟧') (𝟙 Y)) ≫ B.map (Prod.mkHom (𝟙 (X'⟦n⟧)) g) by
          simp [← B.map_comp]]
      rw [Category.assoc, ← h₁, ← Category.assoc, h₂, Category.assoc,
        ← CategoryTheory.Functor.map_comp, ← B.map_comp]
      simp)
  second n := NatIso.ofComponents
    (fun X ↦ (((Functor.curry.obj B).obj X.1).commShiftIso n).app X.2) (by
      rintro ⟨X, Y⟩ ⟨X', Y'⟩ ⟨f, g⟩
      have h₁ := NatTrans.shift_app_comm ((Functor.curry.obj B).map f) n Y
      have h₂ := (((Functor.curry.obj B).obj X').commShiftIso n).hom.naturality g
      dsimp at h₁ h₂ ⊢
      rw [show B.map (Prod.mkHom f (g⟦n⟧')) =
        B.map (Prod.mkHom f (𝟙 (Y⟦n⟧))) ≫ B.map (Prod.mkHom (𝟙 X') (g⟦n⟧')) by
          simp [← B.map_comp]]
      rw [Category.assoc, h₂, ← Category.assoc, ← h₁, Category.assoc,
        ← CategoryTheory.Functor.map_comp, ← B.map_comp]
      simp)

/-- The inherited resolution shift of the existing exact derived slice restriction.
Source: Stacks Tags 08FI and 07A4; signed representative calculation
(blueprint: lem-weil-pbc-ringed-slice-comparisons-shift). -/
instance ringedSliceRestrictionCommShift
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (A : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings A))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((localCoefficientRings A).over U))] :
    (ringedSliceRestriction.{u, w} A U).CommShift ℤ :=
  letI := (ringedOverFunctor_exactGeneral.{u, u, u, u} (localCoefficientRings A) U).1
  letI := (ringedOverFunctor_exactGeneral.{u, u, u, u} (localCoefficientRings A) U).2.1
  letI := (ringedOverFunctor_exactGeneral.{u, u, u, u} (localCoefficientRings A) U).2.2
  inferInstanceAs ((overFunctor.{u} (localCoefficientRings A) U).mapDerivedCategory.CommShift ℤ)

section TensorExt

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Sheaf J CommRingCat.{u})

-- Total-tensor maps are determined by the sheafified pure-tensor generators.
private theorem tensorGenerator_ext
    (P Q F : CochainComplex (SheafOfModules.{u} ((sheafCompose J (forget₂
      CommRingCat.{u} RingCat.{u})).obj A)) ℤ)
    (φ ψ : (coefficientTotalTensor.{u, u, u} J A).obj (P, Q) ⟶ F)
    (h : ∀ (p q k : ℤ) (hpq : p + q = k) (V : Cᵒᵖ)
      (x : (P.X p).val.obj V) (y : (Q.X q).val.obj V),
      (φ.f k).val.app V (coefficientTensorGenerator.{u, u, u} J A P Q p q k hpq V x y) =
        (ψ.f k).val.app V (coefficientTensorGenerator.{u, u, u} J A P Q p q k hpq V x y)) :
    φ = ψ := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients A
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients A
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients A
  apply HomologicalComplex.hom_ext
  intro k
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification (R := A) (P.X p) (Q.X q)).inv).mp
  let adj := PresheafOfModules.sheafificationAdjunction.{u}
    (𝟙 ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj A).obj)
  apply (adj.homEquiv ((P.X p).val ⊗ (Q.X q).val) (F.X k)).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h p q k hpq V x y

end TensorExt

section Tensor

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Sheaf J CommRingCat.{u})
  [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings A))]
  (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, w} J A))
  (T : CoefficientTensorModels.{u, u, u, w} J A S)
  [(Functor.curry.obj S.tensor).CommShift₂Int]

/-- The specified tensor shifts are the unsigned first and signed second total shifts.
The formulas on sheafified pure-tensor generators determine the chain isomorphisms;
the displayed localization squares fix the derived shifts, including their signs.
Source: Stacks Tags 08FI and 07A4; signed representative calculation
(blueprint: lem-weil-pbc-ringed-slice-comparisons-shift). -/
def RingedSliceTensorShiftNormalized : Prop :=
  (∀ (P Q : CochainComplex (SheafOfModules.{u} (localCoefficientRings A)) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q) (n : ℤ),
    ∃ hpn : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) (P⟦n⟧),
    ∃ γ : (coefficientTotalTensor.{u, u, u} J A).obj (P⟦n⟧, Q) ≅
        ((coefficientTotalTensor.{u, u, u} J A).obj (P, Q))⟦n⟧,
      (∀ (p q k : ℤ) (h : p + q = k) (h' : (p + n) + q = k + n) (V : Cᵒᵖ)
        (x : (P.X (p + n)).val.obj V)
        (y : (Q.X q).val.obj V),
        (γ.hom.f k).val.app V
          (coefficientTensorGenerator.{u, u, u} J A (P⟦n⟧) Q p q k h V x y) =
          coefficientTensorGenerator.{u, u, u} J A P Q (p + n) q (k + n) h' V x y) ∧
      (T.iso J A S (P⟦n⟧) Q hpn hq).hom ≫
        S.tensor.map (Prod.mkHom ((DerivedCategory.Q.commShiftIso n).hom.app P) (𝟙 _)) ≫
        (((Functor.curry.obj S.tensor).flip.obj (DerivedCategory.Q.obj Q)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj P) =
      DerivedCategory.Q.map γ.hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((coefficientTotalTensor.{u, u, u} J A).obj (P, Q)) ≫
        (T.iso J A S P Q hp hq).hom⟦n⟧') ∧
  (∀ (P Q : CochainComplex (SheafOfModules.{u} (localCoefficientRings A)) ℤ)
    (hp : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) P)
    (hq : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) Q) (n : ℤ),
    ∃ hqn : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := A) (Q⟦n⟧),
    ∃ γ : (coefficientTotalTensor.{u, u, u} J A).obj (P, Q⟦n⟧) ≅
        ((coefficientTotalTensor.{u, u, u} J A).obj (P, Q))⟦n⟧,
      (∀ (p q k : ℤ) (h : p + q = k) (h' : p + (q + n) = k + n) (V : Cᵒᵖ)
        (x : (P.X p).val.obj V)
        (y : (Q.X (q + n)).val.obj V),
        (γ.hom.f k).val.app V
          (coefficientTensorGenerator.{u, u, u} J A P (Q⟦n⟧) p q k h V x y) =
          (p * n).negOnePow •
            coefficientTensorGenerator.{u, u, u} J A P Q p (q + n) (k + n) h' V x y) ∧
      (T.iso J A S P (Q⟦n⟧) hp hqn).hom ≫
        S.tensor.map (Prod.mkHom (𝟙 _) ((DerivedCategory.Q.commShiftIso n).hom.app Q)) ≫
        (((Functor.curry.obj S.tensor).obj (DerivedCategory.Q.obj P)).commShiftIso n).hom.app
          (DerivedCategory.Q.obj Q) =
      DerivedCategory.Q.map γ.hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((coefficientTotalTensor.{u, u, u} J A).obj (P, Q)) ≫
        (T.iso J A S P Q hp hq).hom⟦n⟧')

private theorem tensorShiftNormalized_formula
    (s : TensorIntegerShiftComparisons (coefficientTotalTensor.{u, u, u} J A))
    (hs : TotalTensorIntegerShiftFormula J A s)
    (hn : RingedSliceTensorShiftNormalized J A S T) :
    DerivedTensorIntegerShiftFormula J A S T s (tensorShiftComparisons S.tensor) := by
  intro P Q hp hq _ _ n
  constructor
  · intro hpn
    obtain ⟨_, γ, hg, he⟩ := hn.1 P Q hp hq n
    have heq : γ.hom = (s.first n).hom.app (P, Q) := by
      apply tensorGenerator_ext J A (P⟦n⟧) Q
      intro p q k h V x y
      have h' : (p + n) + q = k + n := by omega
      exact (hg p q k h h' V x y).trans (hs.1 P Q n p q k h h' V x y).symm
    simpa only [tensorShiftComparisons, NatIso.ofComponents_hom_app, Iso.app_hom, heq] using he
  · intro hqn
    obtain ⟨_, γ, hg, he⟩ := hn.2 P Q hp hq n
    have heq : γ.hom = (s.second n).hom.app (P, Q) := by
      apply tensorGenerator_ext J A P (Q⟦n⟧)
      intro p q k h V x y
      have h' : p + (q + n) = k + n := by omega
      have hh := hs.2 P Q n p q k h h' V x y
      rw [mul_comm n p] at hh
      exact (hg p q k h h' V x y).trans hh.symm
    simpa only [tensorShiftComparisons, NatIso.ofComponents_hom_app, Iso.app_hom, heq] using he

end Tensor

/-- Both tensor shift squares for the canonical slice comparison, with the other
input fixed. Quantification over normalized models makes the assertion independent
of the presentation of derived tensor. This predicate is applied to both R and S.
Source: Stacks Tags 08FI and 07A4; signed representative calculation
(blueprint: lem-weil-pbc-ringed-slice-comparisons-shift). -/
def RingedSliceTensorShiftCompatibility
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings A))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((localCoefficientRings A).over U))] : Prop :=
  ∀ (S : CoefficientClosedStructure (derivedInternalHomOfUniverses.{u, u, u, w} J A))
    (T : CoefficientTensorModels.{u, u, u, w} J A S)
    (SU : CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{u, u, u, w} (J.over U) (A.over U)))
    (TU : CoefficientTensorModels.{u, u, u, w} (J.over U) (A.over U) SU)
    (d : RingedSliceEvaluationComparisons
      (derivedInternalHomOfUniverses.{u, u, u, w} J A)
      (derivedInternalHomOfUniverses.{u, u, u, w} (J.over U) (A.over U))
      (ringedSliceDerivedRestriction.{u, u, u, w, w} J A U) S SU
      (RingedSliceFlatRestriction.{u, u, u} J A U))
    (_hd : RingedSliceTensorModel.{u, u, u, w, w} J A U S T SU TU d)
    [_s : (Functor.curry.obj S.tensor).CommShift₂Int]
    [_sU : (Functor.curry.obj SU.tensor).CommShift₂Int],
    RingedSliceTensorShiftNormalized J A S T →
    RingedSliceTensorShiftNormalized (J.over U) (A.over U) SU TU →
    ∀ (M N : ringedSiteDerived.{u, w} A) (n : ℤ),
      ((d.rho (M⟦n⟧) N).hom ≫
        SU.tensor.map (Prod.mkHom
          (((ringedSliceRestriction.{u, w} A U).commShiftIso n).hom.app M) (𝟙 _)) ≫
        (((Functor.curry.obj SU.tensor).flip.obj
          ((ringedSliceRestriction.{u, w} A U).obj N)).commShiftIso n).hom.app
            ((ringedSliceRestriction.{u, w} A U).obj M) =
      (ringedSliceRestriction.{u, w} A U).map
        ((((Functor.curry.obj S.tensor).flip.obj N).commShiftIso n).hom.app M) ≫
        ((ringedSliceRestriction.{u, w} A U).commShiftIso n).hom.app
          (S.tensor.obj (M, N)) ≫ (d.rho M N).hom⟦n⟧') ∧
      ((d.rho M (N⟦n⟧)).hom ≫
        SU.tensor.map (Prod.mkHom (𝟙 _)
          (((ringedSliceRestriction.{u, w} A U).commShiftIso n).hom.app N)) ≫
        (((Functor.curry.obj SU.tensor).obj
          ((ringedSliceRestriction.{u, w} A U).obj M)).commShiftIso n).hom.app
            ((ringedSliceRestriction.{u, w} A U).obj N) =
      (ringedSliceRestriction.{u, w} A U).map
        ((((Functor.curry.obj S.tensor).obj M).commShiftIso n).hom.app N) ≫
        ((ringedSliceRestriction.{u, w} A U).commShiftIso n).hom.app
          (S.tensor.obj (M, N)) ≫ (d.rho M N).hom⟦n⟧')

private theorem tensorShiftCompatibility
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (A : Sheaf J CommRingCat.{u}) (U : C)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings A))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((localCoefficientRings A).over U))] :
    RingedSliceTensorShiftCompatibility.{u, w} J A U := by
  intro S T SU TU d hd _ _ hn hnU
  obtain ⟨s, hs⟩ := (total_tensor_integer_shift_models.{u, u, u} J A).2
  obtain ⟨sU, hsU⟩ := (total_tensor_integer_shift_models.{u, u, u} (J.over U) (A.over U)).2
  have h := (slice_tensor_integer_shift_compatibility J A U S T SU TU d hd s sU hs hsU).2
    (tensorShiftComparisons S.tensor) (tensorShiftComparisons SU.tensor)
    (tensorShiftNormalized_formula J A S T s hs hn)
    (tensorShiftNormalized_formula (J.over U) (A.over U) SU TU sU hsU hnU)
  intro M N n
  exact h M N n

/-- The adjunct of the specified coefficient isomorphism, used by the recorded module API.
Source: Stacks Tag 04J0 (blueprint: lem-weil-pbc-ringed-slice-comparisons-shift). -/
def ringedSliceShiftStructuralMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : D ⥤ C) [u.IsContinuous K J]
    {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
    (c : (u.sheafPullback CommRingCat.{u} K J).obj R ≅ S) :
    R ⟶ (u.sheafPushforwardContinuous CommRingCat.{u} K J).obj S :=
  (u.sheafAdjunctionContinuous CommRingCat.{u} K J).homEquiv R S c.hom

/-- The canonical direct-image, inverse-image, and both tensor slice comparisons
commute with every integer shift, with the specified total-tensor signs.
Source: Stacks Tags 08FI and 07A4, representative constructions; the signed-shift
calculation is agent-written (blueprint: lem-weil-pbc-ringed-slice-comparisons-shift).

Proof:
1. Restriction is termwise identity at T -> V, so its shift comparison has identity
components. The differential on K[n] is (-1)^n d. Mathlib's total-tensor shifts
(lem-weil-pbc-total-tensor-integer-shifts) have coefficient 1 in the first input
and (-1)^(np) in the second. Reindexing preserves flat terms and K-flatness:
tensoring a shifted representative with an acyclic complex is a shift of an
acyclic tensor, by these signed isomorphisms (def-pc-kflat-complex).
2. Resolve E by a K-injective I (prop-pur-kinjective-resolutions-exist).
Its restriction is K-injective (lem-pur-kinjective-restrict-localized).
The normalization below is precisely lem-weil-pbc-ringed-slice-derived-comparisons:
beta on QI is induced by the ordinary identity on I(uT). For E[n] use I[n],
valid by lem-weil-pbc-kinjective-shift. Both shift-square paths are identity on
I^(a+n)(uT), with differential (-1)^n d. Localization and naturality extend
the equality to every unbounded E. The specified resolution shifts are fixed
by their compatibility with eta and epsilon (lem-weil-pbc-derived-adjunction-shift).
3. The unit square in RingedSliceAdjunctionSquare identifies the adjunct of
lambda_P with beta_(LP) after restriction of the global unit. Apply the unit
shift equations of lem-weil-pbc-derived-adjunction-shift globally and locally,
Step 2, and naturality of beta at L(P[n]) -> LP[n]. The resulting equality
says the two shifted adjuncts are equal.
4. The adjunction bijection is injective, hence the two lambda shift paths agree
(lem-weil-pbc-adjunction-shift-compatibility-unique). This uses the specified
mate, including its orientation, rather than selecting a new comparison.
5. For either site resolve both tensor inputs by flat-term K-flat P,Q
(lem-pc-kflat-resolution). Restriction preserves this class. The canonical
tensor normalization is RingedSliceTensorModel, from
lem-weil-pbc-ringed-slice-evaluation-transpose: on each (p,q) summand it sends
x tensor y to x tensor y. Use shifted representatives from Step 1.
6. In the first-input square both paths send the summand to the same restricted
pure tensor with coefficient 1; in the second both have coefficient (-1)^(np).
Restriction and the tensor map commute with this scalar. These are chain maps
for the differential in def-pc-tensor-complex-sheaves. Equality passes through Q;
the uniqueness clause of lem-weil-pbc-site-derived-tensor-descent extends it
to arbitrary derived inputs. Do this for R at V and S at u(V), giving all four
squares. No boundedness or nonzero coefficient hypothesis is used. -/
theorem ringedSliceComparisonsShift
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (u : D ⥤ C) [u.IsContinuous K J]
    [PreservesFiniteLimits (u.sheafPullback (Type u) K J)]
    {R : Sheaf K CommRingCat.{u}} {S : Sheaf J CommRingCat.{u}}
    (c : (u.sheafPullback CommRingCat.{u} K J).obj R ≅ S) (V : D)
    [(Over.post (X := V) u).IsContinuous (K.over V) (J.over (u.obj V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings R))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (localCoefficientRings S))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((localCoefficientRings R).over V))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((localCoefficientRings S).over (u.obj V)))]
    (e : RingedSliceDerivedImage.{u, w} u (ringedSliceShiftStructuralMap u c))
    (l : RingedSliceDerivedImage.{u, w} (Over.post (X := V) u)
      (localizedRingedSiteMap u (ringedSliceShiftStructuralMap u c) V))
    (d : RingedSliceAdjunctionSquare e.adjunction l.adjunction
      (ringedSliceRestriction.{u, w} R V) (ringedSliceRestriction.{u, w} S (u.obj V)))
    (_normalized : ∀ I : CochainComplex (SheafOfModules.{u} (localCoefficientRings S)) ℤ,
      (ringedSliceRestriction.{u, w} R V).map (e.eta.app I) ≫
        d.beta.hom.app (DerivedCategory.Q.{w}.obj I) ≫
        l.right.map ((ringedSliceRestrictionFactors.{u, w} S (u.obj V)).hom.app I) =
      (ringedSliceRestrictionFactors.{u, w} R V).hom.app
        (((ringedSliceModulePushforward u (ringedSliceShiftStructuralMap u c)).mapHomologicalComplex
          (.up ℤ)).obj I) ≫
        DerivedCategory.Q.{w}.map
          (ringedSlicePushforwardComplexIso u (ringedSliceShiftStructuralMap u c) V I).hom ≫
        l.eta.app ((ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj I))
    [e.left.CommShift ℤ] [e.right.CommShift ℤ]
    [l.left.CommShift ℤ] [l.right.CommShift ℤ]
    [NatTrans.CommShift e.epsilon ℤ] [NatTrans.CommShift e.eta ℤ]
    [NatTrans.CommShift l.epsilon ℤ] [NatTrans.CommShift l.eta ℤ] :
    NatTrans.CommShift d.beta.hom ℤ ∧ NatTrans.CommShift d.lambda.hom ℤ ∧
      RingedSliceTensorShiftCompatibility.{u, w} K R V ∧
      RingedSliceTensorShiftCompatibility.{u, w} J S (u.obj V) := by
  let a := ringedSliceShiftStructuralMap u c
  let F := ringedSliceModulePushforward u a
  let G := ringedSliceModulePushforward (Over.post (X := V) u)
    (localizedRingedSiteMap u a V)
  let r := overFunctor (localCoefficientRings R) V
  let t := overFunctor (localCoefficientRings S) (u.obj V)
  let := (ringedOverFunctor_exactGeneral.{u, u, u, u} (localCoefficientRings R) V).1
  let := (ringedOverFunctor_exactGeneral.{u, u, u, u} (localCoefficientRings R) V).2.1
  let := (ringedOverFunctor_exactGeneral.{u, u, u, u} (localCoefficientRings R) V).2.2
  let := (ringedOverFunctor_exactGeneral.{u, u, u, u}
    (localCoefficientRings S) (u.obj V)).1
  let := (ringedOverFunctor_exactGeneral.{u, u, u, u}
    (localCoefficientRings S) (u.obj V)).2.1
  let := (ringedOverFunctor_exactGeneral.{u, u, u, u}
    (localCoefficientRings S) (u.obj V)).2.2
  let := e.isRightDerived
  let := l.isRightDerived
  obtain ⟨I, ηI, hI⟩ :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u} J S).2.2
  obtain ⟨I', ηI', hI'⟩ :=
    (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u}
      (J.over (u.obj V)) (S.over (u.obj V))).2.2
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u} J S).1
  let := (grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u, u, u}
    (J.over (u.obj V)) (S.over (u.obj V))).1
  have hb := derivedSquare_shift_on_kinjectives F G t r (Iso.refl _)
    (fun K ↦ ⟨I.obj K, (hI K).2.1, ηI.app K, (hI K).1⟩)
    (fun K ↦ ⟨I'.obj K, (hI' K).2.1, ηI'.app K, (hI' K).1⟩)
    (fun K hK ↦ by
      let := hK
      exact isKInjective_restrict_localized _ _ inferInstance K)
    e.right l.right e.eta l.eta
    (fun K hK ↦ by
      let := hK
      exact (CategoryTheory.derives F).isIso_of_isRightDerivedFunctor e.eta
        (CochainComplex.KInjectives.mk K))
    (fun K hK ↦ by
      let := hK
      exact (CategoryTheory.derives G).isIso_of_isRightDerivedFunctor l.eta
        (CochainComplex.KInjectives.mk K))
    (fun K _ n ↦ (NatTrans.shift_app_comm e.eta n K).symm)
    (fun K _ n ↦ (NatTrans.shift_app_comm l.eta n K).symm)
    d.beta (by
      intro K
      exact iso_normalization_cancel l.right
        ((ringedSliceRestrictionFactors.{u, w} R V).app
          ((F.mapHomologicalComplex (.up ℤ)).obj K))
        ((ringedSliceRestrictionFactors.{u, w} S (u.obj V)).app K)
        ((ringedSliceRestriction R V).map (e.eta.app K))
        (d.beta.hom.app (DerivedCategory.Q.obj K))
        (DerivedCategory.Q.map (ringedSlicePushforwardComplexIso.{u} u a V K).hom)
        (l.eta.app ((ringedSliceComplexRestriction.{u, u, u} J S (u.obj V)).obj K))
        (_normalized K))
  have hbeta : NatTrans.CommShift d.beta.hom ℤ := by
    constructor
    intro n
    ext E
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.commShiftIso_comp_hom_app, ringedSliceRestrictionCommShift,
      ringedSliceRestriction, ringedSliceDerivedRestriction, ringedDerivedRestrictionGeneral]
      using (hb.2.1 n E).symm
  clear hb I ηI hI I' ηI' hI'
  let := e.isLeftDerived.isRightKanExtension
  let := l.isLeftDerived.isRightKanExtension
  refine ⟨hbeta, ?_, ?_, ?_⟩
  · have hunit := normalized_unit_commShift DerivedCategory.Q DerivedCategory.Q
      ((ringedSliceModulePullback u a).mapHomologicalComplex (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) e.left e.right
      ((ringedSliceModuleAdjunction u a).mapHomologicalComplex (.up ℤ))
      e.adjunction e.epsilon e.eta e.normalized
    have hunit' := normalized_unit_commShift DerivedCategory.Q DerivedCategory.Q
      ((ringedSliceModulePullback (Over.post (X := V) u)
        (localizedRingedSiteMap u a V)).mapHomologicalComplex (.up ℤ))
      (G.mapHomologicalComplex (.up ℤ)) l.left l.right
      ((ringedSliceModuleAdjunction (Over.post (X := V) u)
        (localizedRingedSiteMap u a V)).mapHomologicalComplex (.up ℤ))
      l.adjunction l.epsilon l.eta l.normalized
    let := hbeta
    let := hunit
    let := hunit'
    have hlam (P : ringedSiteDerived.{u, w} R) :
        d.lambda.hom.app P =
          l.left.map ((ringedSliceRestriction R V).map (e.adjunction.unit.app P) ≫
            d.beta.hom.app (e.left.obj P)) ≫
              l.adjunction.counit.app ((ringedSliceRestriction S (u.obj V)).obj
                (e.left.obj P)) := by
      apply (l.adjunction.homEquiv _ _).injective
      rw [← l.adjunction.homEquiv_counit (g :=
        (ringedSliceRestriction R V).map (e.adjunction.unit.app P) ≫
          d.beta.hom.app (e.left.obj P))]
      dsimp only [Functor.comp_obj, Functor.id_obj]
      rw [Equiv.apply_symm_apply]
      have h := congrArg (fun f ↦ f ≫ l.right.map (d.lambda.hom.app P)) (d.unit P)
      simpa only [Category.assoc, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id_app,
        Functor.comp_obj, Functor.id_obj, CategoryTheory.Functor.map_id, Category.comp_id,
        Adjunction.homEquiv_unit] using h.symm
    exact shift_mate_commShift e.adjunction l.adjunction
      (ringedSliceRestriction R V) (ringedSliceRestriction S (u.obj V))
      d.beta.hom d.lambda.hom hlam
  · exact tensorShiftCompatibility K R V
  · exact tensorShiftCompatibility J S (u.obj V)

end SheafOfModules
