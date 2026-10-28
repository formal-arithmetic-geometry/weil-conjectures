/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B5
-/
module

public import Sheaf.SixFunctors.IntegralDualizingRoosModel
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence

/-! # Uniqueness of the prescribed integral Roos limit

Source: current blueprint prop-coef-integral-dualizing, second proof paragraph;
Stacks 08TC and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]

/- Transport a Roos triangle across compatible object and level isomorphisms. -/
open CategoryTheory.Pretriangulated in
private theorem roosProductTransport
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {A B : ℕ → C} [HasProduct A] [HasProduct B]
    (f : ∀ n, A (n + 1) ⟶ A n) (g : ∀ n, B (n + 1) ⟶ B n)
    {M N : C} (e : M ≅ N) (a : ∀ n, A n ≅ B n)
    (ht : ∀ n, (a (n + 1)).hom ≫ g n = f n ≫ (a n).hom)
    (p : M ⟶ ∏ᶜ A) (δ : (∏ᶜ A) ⟶ M⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f M p δ) :
    ∃ (q : N ⟶ ∏ᶜ B) (δ' : (∏ᶜ B) ⟶ N⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle g N q δ' := by
  let b : (∏ᶜ A) ≅ (∏ᶜ B) :=
    { hom := Limits.Pi.map (fun n ↦ (a n).hom)
      inv := Limits.Pi.map (fun n ↦ (a n).inv)
      hom_inv_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc]
      inv_hom_id := by
        apply Pi.hom_ext
        intro n
        simp [Category.assoc] }
  refine ⟨e.inv ≫ p ≫ b.hom, b.inv ≫ δ ≫ (shiftFunctor C (1 : ℤ)).map e.hom, ?_⟩
  exact (distinguished_iff_of_iso (Triangle.isoMk _ _ e b b
    (by simp) (towerTransitionEndomorphism_natural_backward f g (fun n ↦ (a n).hom) ht).symm
    (by simp))).mp h

/-- Rewrite a commuting comparison square using the inverse vertical isomorphisms. -/
private theorem invertComparisonSquare
    {C : Type*} [Category C] {A B A' B' : C}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ≅ A') (b : B ≅ B')
    (h : f ≫ b.hom = a.hom ≫ g) : a.inv ≫ f = g ≫ b.inv := by
  calc
    a.inv ≫ f = a.inv ≫ (f ≫ b.hom) ≫ b.inv := by simp [Category.assoc]
    _ = g ≫ b.inv := by rw [h]; simp [Category.assoc]

/-- The strict derived-limit specification gives the canonical evaluation Roos triangle.
The comparison follows the private evaluation/product transport in IntegralDualizingRoosModel,
but uses the published normalized evaluation functors directly. -/
private theorem canonicalRoosTriangle (Y : Scheme.{u})
    (Z : DerivedCategory (ℕᵒᵖ ⥤
      ringedSiteModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E Y))) :
    let A := ringedSiteModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E Y)
    let RF := (ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
      (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose
    -- Both category presentations need the same witness during product elaboration.
    let : HasCountableProducts (DerivedCategory A) :=
      integralOperationsDerivedCountableProducts l E Y
    let : HasCountableProducts (completedIntegralDerivedCategory l E Y D hl) :=
      integralOperationsDerivedCountableProducts l E Y
    ∃ (p : RF.obj Z ⟶ ∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E Y D hl n).obj Z)
      (δ : (∏ᶜ fun n : ℕ ↦ (normalizedDVRTowerEvaluation l E Y D hl n).obj Z) ⟶
        (RF.obj Z)⟦(1 : ℤ)⟧),
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (normalizedDVRTowerTransition l E Y D hl n.le_succ).app Z)
        (RF.obj Z) p δ := by
  let A := ringedSiteModules.{u + 1} (completedIntegralCoefficientSheafUnrestricted l E Y)
  let C := DerivedCategory.Q.objPreimage Z
  let z : DerivedCategory.Q.obj C ≅ Z := DerivedCategory.Q.objObjPreimageIso Z
  obtain ⟨η, _, _, _, hshift, hproducts, F, ε, p, δ, _, hroos, _⟩ :=
    (ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
      (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose_spec
  let ev (n : ℕ) := (evaluation ℕᵒᵖ A).obj (op n)
  let tc (n : ℕ) := (NatTrans.mapHomologicalComplex
    ((evaluation ℕᵒᵖ A).map (homOfLE n.le_succ).op) (.up ℤ)).app C
  let c (n : ℕ) : (F.obj (DerivedCategory.Q.obj C)).obj (op n) ≅
      DerivedCategory.Q.obj ((ev n).mapHomologicalComplex (.up ℤ) |>.obj C) :=
    (ε.app C).app (op n)
  have hc (n : ℕ) : (c (n + 1)).hom ≫ DerivedCategory.Q.map (tc n) =
      (F.obj (DerivedCategory.Q.obj C)).map (homOfLE n.le_succ).op ≫ (c n).hom := by
    exact ((ε.hom.app C).naturality (homOfLE n.le_succ).op).symm
  let a (n : ℕ) : (F.obj (DerivedCategory.Q.obj C)).obj (op n) ≅
      (normalizedDVRTowerEvaluation l E Y D hl n).obj Z :=
    c n ≪≫ ((ev n).mapDerivedCategoryFactors.app C).symm ≪≫
      (normalizedDVRTowerEvaluation l E Y D hl n).mapIso z
  have ht (n : ℕ) :
      (a (n + 1)).hom ≫ (normalizedDVRTowerTransition l E Y D hl n.le_succ).app Z =
        (F.obj (DerivedCategory.Q.obj C)).map (homOfLE n.le_succ).op ≫ (a n).hom := by
    have hf : (normalizedDVRTowerTransition l E Y D hl n.le_succ).app
        (DerivedCategory.Q.obj C) ≫ (ev n).mapDerivedCategoryFactors.hom.app C =
      (ev (n + 1)).mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map (tc n) := by
      dsimp only [ev, A, tc]
      simp only [normalizedDVRTowerTransition, completedIntegralModuleSheaves,
        completedIntegralCoefficientSheaf, Localization.liftNatTrans_app,
        Localization.Lifting.iso, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
      rfl
    have hf' : (ev (n + 1)).mapDerivedCategoryFactors.inv.app C ≫
        (normalizedDVRTowerTransition l E Y D hl n.le_succ).app (DerivedCategory.Q.obj C) =
        DerivedCategory.Q.map (tc n) ≫ (ev n).mapDerivedCategoryFactors.inv.app C :=
      invertComparisonSquare _ _ ((ev (n + 1)).mapDerivedCategoryFactors.app C)
        ((ev n).mapDerivedCategoryFactors.app C) hf
    dsimp only [a, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Iso.app,
      Functor.mapIso_hom]
    rw [Category.assoc, Category.assoc,
      (normalizedDVRTowerTransition l E Y D hl n.le_succ).naturality z.hom]
    rw [reassoc_of% hf']
    simpa only [Category.assoc] using congrArg
      (fun k ↦ k ≫ (ev n).mapDerivedCategoryFactors.inv.app C ≫
        (normalizedDVRTowerEvaluation l E Y D hl n).map z.hom) (hc n)
  let := hproducts
  let hp : HasProduct (fun n : ℕ ↦ (F.obj (DerivedCategory.Q.obj C)).obj (op n)) :=
    inferInstance
  have hr := hroos (DerivedCategory.Q.obj C)
  let : HasCountableProducts (DerivedCategory A) :=
    integralOperationsDerivedCountableProducts l E Y
  let : HasCountableProducts (completedIntegralDerivedCategory l E Y D hl) :=
    integralOperationsDerivedCountableProducts l E Y
  exact roosProductTransport _ _
    (((ringedStrictTowerHomotopyLimitOfUniverses.{u + 2, u + 1, u, u}
      (ProEt.topology Y) (completedIntegralCoefficientSheafUnrestricted l E Y)
      (completedIntegralCoefficient_mul_commUnrestricted l E Y)).choose).mapIso z) a ht
    (p (DerivedCategory.Q.obj C)) (δ (DerivedCategory.Q.obj C)) hr

-- Preserve the existing geometric hypotheses, although Roos uniqueness does not use them.
set_option linter.unusedSectionVars false in
/-- A prescribed Roos presentation is uniquely isomorphic to the chosen derived limit.

Source: Stacks 08TC and 0941 (blueprint: lem-coef-integral-dualizing-mapping-tower-limit).

Proof: unpack the supplied triangle in `IntegralDualizingLimitPresentation` and the
canonical Roos triangle for `integralDualizingLimit`.  Both triangles have the same
successor transition endomorphism and product object.  Rotate both distinguished
triangles and apply the triangulated triangle-isomorphism theorem with the identity on
the product term.  The resulting isomorphism of the third terms, transported back
through the shift equivalence, is the required isomorphism between `M.obj` and the
chosen limit.  The extra counit clauses in the presentation are irrelevant to this
uniqueness statement.
(blueprint: lem-coef-integral-dualizing-mapping-tower-limit-roos-iso). -/
theorem integralDualizing_mapping_tower_limit_roos_iso
    (T : NormalizedDVRTower l E X D hl)
    (M : sfIntegralConstructibleCategory l E X)
    (hM : IntegralDualizingLimitPresentation l E D hl X T M.obj) :
    Nonempty (M.obj ≅ (integralDualizingLimit l E X).obj T.tower) := by
  let : HasCountableProducts (completedIntegralDerivedCategory l E X D hl) :=
    integralOperationsDerivedCountableProducts l E X
  obtain ⟨p, δ, hp, _, _⟩ := hM
  obtain ⟨q, ε, hq⟩ := canonicalRoosTriangle D l hl E X T.tower
  exact (exists_isDerivedLimit_and_iso _ _).2 _ _ ⟨p, δ, hp⟩ ⟨q, ε, hq⟩

end WeilConjectures
