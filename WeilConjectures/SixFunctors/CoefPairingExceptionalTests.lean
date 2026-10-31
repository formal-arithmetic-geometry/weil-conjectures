/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralDualizingSystemAdjunctionMap
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction

/-! # Testing exceptional transposes through adjunctions

Source: prop-asd-internal-adjunction, the chain of Hom bijections;
prop-coef-integral-dualizing, proof paragraph 2.
(blueprint: lem-coef-exceptional-transpose-tests).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe a b c d v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace CategoryTheory.CoefPairingFrame
variable {A : Type a} {B : Type b} {C : Type c} {D : Type d}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  {HA : Aᵒᵖ × A ⥤ A} {HC : Cᵒᵖ × C ⥤ C}
  (SA : WeilConjectures.CoefficientClosedStructure HA)
  (SC : WeilConjectures.CoefficientClosedStructure HC)
  {TB : B × B ⥤ B} {TD : D × D ⥤ D}
  {J : A ⥤ B} {P : B ⥤ C} {R : C ⥤ D} {RX : A ⥤ D}
  (F : CoefPairingFrame SA.tensor TB SC.tensor TD J P R RX)

/-- The pullback of a sections test object, before tensoring with the input.
Source: prop-asd-internal-adjunction, first Hom bijection
(blueprint: lem-coef-exceptional-transpose-tests). -/
abbrev testPull : D ⥤ A := F.sstar ⋙ F.pstar ⋙ F.jstar

/-- The proper projection followed by inverse open tensor comparison.
Source: prop-asd-internal-adjunction, projection-formula step
(blueprint: lem-coef-exceptional-transpose-tests). -/
def testProjection (H : D) (M : A) :
    SC.tensor.obj (F.sstar.obj H, P.obj (J.obj M)) ⟶
      P.obj (J.obj (SA.tensor.obj (F.testPull.obj H, M))) :=
  leftMate SC.tensor TB F.pstar P F.properAdjunction F.properTensor
      (F.sstar.obj H) (J.obj M) ≫
    P.map (F.openTensor (F.pstar.obj (F.sstar.obj H)) M).inv

private theorem open_inv_naturality (L L' : B) (M : A) (f : L ⟶ L') :
    TB.map (Prod.mkHom f (𝟙 (J.obj M))) ≫ (F.openTensor L' M).inv =
      (F.openTensor L M).inv ≫ J.map (SA.tensor.map (Prod.mkHom (F.jstar.map f) (𝟙 M))) := by
  have hn : J.map (SA.tensor.map (Prod.mkHom (F.jstar.map f) (𝟙 M))) ≫
      (F.openTensor L' M).hom = (F.openTensor L M).hom ≫
        TB.map (Prod.mkHom f (𝟙 (J.obj M))) := by
    apply (F.openAdjunction.homEquiv _ _).injective
    rw [F.openAdjunction.homEquiv_naturality_left,
      F.openAdjunction.homEquiv_naturality_right,
      F.openTensor_adjunct, F.openTensor_adjunct]
    have hh := F.restrictionTensor.inv.naturality (Prod.mkHom f (𝟙 (J.obj M)))
    dsimp only [Functor.comp_map, Functor.prod_map] at hh
    rw [Category.assoc, ← hh]
    simp only [← Category.assoc, ← Functor.map_comp]
    congr 2
    ext <;> simp
  apply (cancel_epi (F.openTensor L M).hom).mp
  rw [← Category.assoc, ← hn]
  simp

private theorem testProjection_naturality (H H' : D) (f : H ⟶ H') (M : A) :
    SC.tensor.map (Prod.mkHom (F.sstar.map f) (𝟙 _)) ≫ F.testProjection SA SC H' M =
      F.testProjection SA SC H M ≫
        P.map (J.map (SA.tensor.map (Prod.mkHom (F.testPull.map f) (𝟙 M)))) := by
  let flip := (Functor.flipping (C := C) (D := C) (E := B)).functor
  let w := F.properAdjunction.rightAdjointProjectionMap
    (T_C := (Functor.curryObj TB).flip) (T_D := (Functor.curryObj SC.tensor).flip)
    (flip.map (Functor.curry.map F.properTensor.hom) ≫
      (flip.mapIso (Functor.curryObjProdComp F.pstar F.pstar TB)).hom)
  have hn := NatTrans.naturality (w.app (J.obj M)) (F.sstar.map f)
  have hn' : SC.tensor.map (Prod.mkHom (F.sstar.map f) (𝟙 _)) ≫
      leftMate SC.tensor TB F.pstar P F.properAdjunction F.properTensor
        (F.sstar.obj H') (J.obj M) =
    leftMate SC.tensor TB F.pstar P F.properAdjunction F.properTensor
        (F.sstar.obj H) (J.obj M) ≫
      P.map (TB.map (Prod.mkHom (F.pstar.map (F.sstar.map f)) (𝟙 _))) := hn
  dsimp only [testProjection]
  rw [← Category.assoc, hn', Category.assoc, ← P.map_comp]
  rw [open_inv_naturality SA SC F]
  rw [P.map_comp, Category.assoc]
  rfl

/-- Removing the two transposes identifies postcomposition with the exceptional map
with projection, compact-support application, and the trace. This is an equation
for each test arrow, with no invertibility assertion.
Source: prop-asd-internal-adjunction, final evaluation/counit calculation
(blueprint: lem-coef-exceptional-transpose-tests).
Proof: use naturality of both adjunction Hom equivalences. Move the test arrow
through the proper projection and the inverse open comparison. The remaining
source counit is exactly the inverse source-sections adjunction. -/
theorem exceptionalMap_test (H : D) (M Q : A) (U : C)
    (t : P.obj (J.obj Q) ⟶ U) (f : H ⟶ RX.obj (HA.obj (op M, Q))) :
    (SC.transpose _ _ _).symm
      ((F.sectionsAdjunction.homEquiv _ _).symm
        (f ≫ exceptionalMap SA SC F Q U t M)) =
      F.testProjection SA SC H M ≫ P.map (J.map
        ((SA.transpose _ _ _).symm ((F.sourceAdjunction.homEquiv _ _).symm f))) ≫ t := by
  let := SA.monoidal
  let := SC.monoidal
  rw [exceptionalMap, ← F.sectionsAdjunction.homEquiv_naturality_left,
    Equiv.symm_apply_apply]
  have htranspose :
      F.sstar.map f ≫ SC.transpose _ _ _ (basePairing SA SC F M Q ≫ t) =
        SC.transpose _ _ _
          (SC.tensor.map (Prod.mkHom (F.sstar.map f) (𝟙 _)) ≫
            (basePairing SA SC F M Q ≫ t)) := by
    have h := ((SC.adjunction (P.obj (J.obj M))).homEquiv_naturality_left
      (F.sstar.map f) (basePairing SA SC F M Q ≫ t)).symm
    change F.sstar.map f ≫ SC.transpose _ _ _ (basePairing SA SC F M Q ≫ t) =
      SC.transpose _ _ _ ((F.sstar.map f ▷ _) ≫ (basePairing SA SC F M Q ≫ t)) at h
    simpa only [WeilConjectures.CoefficientClosedStructure.tensor,
      MonoidalCategory.tensor, tensorHom_id] using h
  rw [htranspose, Equiv.symm_apply_apply]
  change SC.tensor.map (Prod.mkHom (F.sstar.map f) (𝟙 _)) ≫
      (basePairing SA SC F M Q ≫ t) = _
  have hb : basePairing SA SC F M Q =
      F.testProjection SA SC (RX.obj (HA.obj (op M, Q))) M ≫
        P.map (J.map
          (SA.tensor.map (Prod.mkHom (F.sourceAdjunction.counit.app _) (𝟙 M)) ≫
            SA.evaluation M Q)) := by
    simp only [basePairing, testProjection, Category.assoc]
  rw [hb]
  simp only [Category.assoc]
  rw [← Category.assoc (SC.tensor.map _)
    (F.testProjection SA SC (RX.obj (HA.obj (op M, Q))) M)]
  rw [testProjection_naturality SA SC F]
  have hs : SA.tensor.map (Prod.mkHom (F.testPull.map f) (𝟙 M)) ≫
      (SA.tensor.map (Prod.mkHom (F.sourceAdjunction.counit.app _) (𝟙 M)) ≫
        SA.evaluation M Q) =
      (SA.transpose _ _ _).symm ((F.sourceAdjunction.homEquiv _ _).symm f) := by
    change _ =
      (F.testPull.map f ≫ F.sourceAdjunction.counit.app (HA.obj (op M, Q))) ▷ M ≫
        SA.evaluation M Q
    simp only [comp_whiskerRight, WeilConjectures.CoefficientClosedStructure.tensor,
      MonoidalCategory.tensor, tensorHom_id, Category.assoc]
  have hm := congrArg (fun g ↦ P.map (J.map g)) hs
  simp only [Functor.map_comp] at hm
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun g ↦ F.testProjection SA SC H M ≫ g ≫ t) hm

/-- The two middle geometric steps imply bijectivity on a sections test object.
Source: prop-asd-internal-adjunction, displayed chain of Hom bijections
(blueprint: lem-coef-exceptional-transpose-tests).
Proof: source-sections and tensor-Hom adjunctions are bijections. Apply the
trace adjunction to their output, precompose with the invertible projection,
and transpose back by the base closed and sections adjunctions. The previous
test-arrow equation identifies this composite with the specified exceptional map. -/
theorem exceptionalMap_test_bijective (H : D) (M Q : A) (U : C)
    (t : P.obj (J.obj Q) ⟶ U)
    (hproj : IsIso (F.testProjection SA SC H M))
    (htrace : Function.Bijective (fun g : SA.tensor.obj (F.testPull.obj H, M) ⟶ Q ↦
      P.map (J.map g) ≫ t)) :
    Function.Bijective (fun f : H ⟶ RX.obj (HA.obj (op M, Q)) ↦
      f ≫ exceptionalMap SA SC F Q U t M) := by
  let eA := (F.sourceAdjunction.homEquiv H (HA.obj (op M, Q))).symm.trans
    (SA.transpose _ M Q).symm
  let eC := (Iso.homCongr (asIso (F.testProjection SA SC H M)) (Iso.refl U)).symm
  let eB := (SC.transpose _ (P.obj (J.obj M)) U).trans
    (F.sectionsAdjunction.homEquiv H (HC.obj (op (P.obj (J.obj M)), U)))
  have he : (fun f : H ⟶ RX.obj (HA.obj (op M, Q)) ↦
      f ≫ exceptionalMap SA SC F Q U t M) =
      fun f ↦ eB (eC (P.map (J.map (eA f)) ≫ t)) := by
    funext f
    apply (F.sectionsAdjunction.homEquiv _ _).symm.injective
    apply (SC.transpose _ _ _).symm.injective
    simpa [eA, eB, eC, Iso.homCongr] using exceptionalMap_test SA SC F H M Q U t f
  rw [he]
  exact eB.bijective.comp (eC.bijective.comp (htrace.comp eA.bijective))
end CategoryTheory.CoefPairingFrame

namespace WeilConjectures
universe u
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Additivity of the ordinary left adjoint of scalar tower evaluation.
Source: additivity of adjoints (blueprint: lem-coef-exceptional-transpose-tests). -/
instance coefPairingEvaluationLeft_additive (n : ℕ) :
    (evaluationLeftAdjoint (ModuleCat.{u + 1} (coefTraceRing l E)) (op n)).Additive :=
  (evaluationAdjunctionRight _ (op n)).left_adjoint_additive

/-- Exactness of the ordinary representable tower test functor.
Source: Stacks 0941 (blueprint: lem-coef-exceptional-transpose-tests).
Proof: each indexing type is subsingleton, so its coproduct functor is exact.
Limits of towers are pointwise. -/
instance coefPairingEvaluationLeft_limits (n : ℕ) :
    PreservesFiniteLimits
      (evaluationLeftAdjoint (ModuleCat.{u + 1} (coefTraceRing l E)) (op n)) := by
  classical
  let A := ModuleCat.{u + 1} (coefTraceRing l E)
  let G := evaluationLeftAdjoint A (op n)
  have (m : ℕᵒᵖ) : PreservesFiniteLimits (G ⋙ (evaluation ℕᵒᵖ A).obj m) := by
    let e : G ⋙ (evaluation ℕᵒᵖ A).obj m ≅
        Functor.const (Discrete (op n ⟶ m)) ⋙ colim :=
      NatIso.ofComponents (fun X ↦ Iso.refl _) (by
        intro X Y f
        apply Sigma.hom_ext
        intro i
        simp [G, evaluationLeftAdjoint]
        rfl)
    exact preservesFiniteLimits_of_natIso e.symm
  exact ⟨fun J _ _ ↦
    preservesLimitsOfShape_of_evaluation G J (fun m ↦ inferInstance)⟩

/-- Exact finite evaluation has a derived left adjoint. The adjunction determines
its values and arrows; its ordinary value at m is a coproduct indexed by n to m.
Source: Stacks 0941, 05RU (blueprint: lem-coef-exceptional-transpose-tests).
Proof: derive the ordinary evaluation adjunction of exact additive functors. -/
def coefPairingEvaluationLeft (n : ℕ) :
    DerivedCategory (ModuleCat.{u + 1} (coefTraceRing l E)) ⥤ coefPairingDerived l E := by
  letI := (evaluationAdjunctionRight
    (ModuleCat.{u + 1} (coefTraceRing l E)) (op n)).isLeftAdjoint
  exact (evaluationLeftAdjoint (ModuleCat.{u + 1} (coefTraceRing l E))
    (op n)).mapDerivedCategory

/-- The exact representable test and finite evaluation are adjoint.
Source: Stacks 0941, 05RU (blueprint: lem-coef-exceptional-transpose-tests). -/
def coefPairingEvaluationAdjunction (n : ℕ) :
    coefPairingEvaluationLeft l E n ⊣ coefPairingDerivedEvaluation l E n := by
  letI := (evaluationAdjunctionRight
    (ModuleCat.{u + 1} (coefTraceRing l E)) (op n)).isLeftAdjoint
  exact (evaluationAdjunctionRight _ (op n)).mapDerivedCategoryAdjunction

end WeilConjectures
