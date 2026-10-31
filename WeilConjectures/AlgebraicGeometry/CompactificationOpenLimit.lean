/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimitSupport

import all WeilConjectures.AlgebraicGeometry.CompletedOpenEndpointLimitTransport
import all WeilConjectures.AlgebraicGeometry.CompletedDirectImageLimits
import all WeilConjectures.AlgebraicGeometry.ConstantTowerDirectImageNormalization

/-! # Open extension and fixed-coefficient strict limits
Source: blueprint direct-image proof, paragraph (2); Stacks 09BP.
(blueprint: lem-sp-compactification-open-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Evaluate the actual constant-tower/limit counit using the canonical exact factors. -/
private def counitProjection (T : Scheme.{u}) (n : ℕ) :
    coefficientConstantTowerLimit l E T ⟶ coefficientConstantTowerEvaluation l E T n where
  app M := (constantEvaluationIso (scalarReductionSource l E T) (op n)).inv.app
      ((coefficientConstantTowerLimit l E T).obj M) ≫
    (coefficientConstantTowerEvaluation l E T n).map
      ((cbcRealizationLimitAdj T ((PurCompactSupport.completed l E).ring T)).counit.app M)
  naturality M N a := by
    let V := coefficientConstantTowerEvaluation l E T n
    let L := coefficientConstantTowerLimit l E T
    let C := (Functor.const ℕᵒᵖ : scalarReductionSource l E T ⥤ _).mapDerivedCategory
    let e := constantEvaluationIso (scalarReductionSource l E T) (op n)
    have hn := e.inv.naturality (L.map a)
    change L.map a ≫ e.inv.app (L.obj N) =
      e.inv.app (L.obj M) ≫ V.map (C.map (L.map a)) at hn
    change L.map a ≫ (e.inv.app (L.obj N) ≫ V.map _) =
      (e.inv.app (L.obj M) ≫ V.map _) ≫ V.map a
    rw [← Category.assoc, hn, Category.assoc, ← V.map_comp]
    erw [(cbcRealizationLimitAdj T
      ((PurCompactSupport.completed l E).ring T)).counit.naturality]
    simp only [V.map_comp, Category.assoc, Functor.id_map]

/-- The prescribed K-injective normalization uniquely identifies the counit projection. -/
private theorem counitProjection_eq (T : Scheme.{u}) (n : ℕ) :
    counitProjection l E T n = coefficientConstantTowerProjection l E T n := by
  apply (coefficientConstantTowerProjection_exists l E T n).choose_spec.2
  intro I hI
  let L : Fixed l E T ⥤ scalarReductionSource l E T := lim
  have hu : L.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I) = L.rightDerivedFunctorUnitQ I := by
    dsimp only [Functor.rightDerivedFunctorUnitQ]
    erw [AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.quotient_inv_id,
      AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.quotient_hom_id,
      L.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  have h := constantLimit_projection_unit (scalarReductionSource l E T) (op n) I
  change L.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) ≫
    (counitProjection l E T n).app (DerivedCategory.Q.obj I) = _ at h
  rw [hu, L.rightDerivedFunctorUnitQ_eq] at h
  apply (cancel_epi (L.rightDerivedFunctorObjQIso I).inv).mp
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- Exact localization preserves the ordinary constant/open/evaluation identity. -/
private theorem open_constant_evaluation {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] (n : ℕ) (M : Integral l E X) :
    (coefficientConstantTowerEvaluation l E Z n).map
        ((cbcRealizationConst (openOrd l E j)).hom.app M) ≫
      (fixedOpenEvaluation l E j n).hom.app
        (((Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤ _).mapDerivedCategory).obj M) ≫
      (openOrd l E j).mapDerivedCategory.map
        ((constantEvaluationIso (scalarReductionSource l E X) (op n)).hom.app M) =
    (constantEvaluationIso (scalarReductionSource l E Z) (op n)).hom.app
      ((openOrd l E j).mapDerivedCategory.obj M) := by
  let F := openOrd l E j
  let CX := (Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤ _)
  let CZ := (Functor.const ℕᵒᵖ : scalarReductionSource l E Z ⥤ _)
  let EX := fixedEvaluation l E X n
  let EZ := fixedEvaluation l E Z n
  have h := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.exact_triangle_square
    CX CZ F (fixedOpenOrd l E j) EX EZ
    (Functor.compConstIso ℕᵒᵖ F).symm (Iso.refl (EX ⋙ F))
    (Functor.constCompEvaluationObj (D := scalarReductionSource l E X) (op n))
    (Functor.constCompEvaluationObj (D := scalarReductionSource l E Z) (op n))
    (fun N ↦ by
      change F.map (𝟙 N) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
      rw [F.map_id, Category.id_comp, Category.comp_id]) M
  have h' : (fixedOpenEvaluation l E j n).inv.app (CX.mapDerivedCategory.obj M) ≫
      EZ.mapDerivedCategory.map ((cbcRealizationConst F).inv.app M) ≫
        (constantEvaluationIso (scalarReductionSource l E Z) (op n)).hom.app
          (F.mapDerivedCategory.obj M) =
      F.mapDerivedCategory.map
        ((constantEvaluationIso (scalarReductionSource l E X) (op n)).hom.app M) := by
    simpa only [Functor.mapDerivedCategorySquareIso, fixedOpenEvaluation,
      cbcRealizationConst, constantEvaluationIso, Functor.mapDerivedCategoryNatIso_symm,
      Functor.mapDerivedCategoryNatIso_refl, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, NatTrans.comp_app, NatTrans.id_app, Category.id_comp, Category.comp_id,
      Category.assoc, EX, EZ, CX, CZ, F] using h
  apply (cancel_epi ((fixedOpenEvaluation l E j n).inv.app
    (CX.mapDerivedCategory.obj M) ≫
      EZ.mapDerivedCategory.map ((cbcRealizationConst F).inv.app M))).mp
  simp only [Category.assoc]
  erw [← EZ.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    EZ.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app_assoc]
  exact h'.symm

/-- The actual constant-diagram open mate is invertible and preserves projections.

Proof. Identify the small pro-etale site of the open with the slice over its open
object. The coefficient pullback identifies the module functor openOrd with extension
by zero on that slice. It is exact and its canonical countable-product comparison is
invertible by proEtaleRingedExtensionByZero_products. Countable products of modules
are exact on both pro-etale sites. Apply exactProductFunctorStrictLimit to these
functors and the fixed-ring total derived limits. Its signed Roos comparison is induced
by the canonical product map on both summands. On strict augmentations this is the
ordinary limit comparison; transposition across const/limit identifies it with the
specified constant-diagram mate openLimit (not merely some isomorphism). The Roos
projection equation, transported by the standard exact localization composition
isomorphisms, is the displayed equality with fixedOpenEvaluation. Invertibility and
the projection identity hold on the whole unbounded category. The empty open, identity
open, zero module and constant tower cases are the same product and mate formulas.
Source: current blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
sk-prop-sp-integral-adjunction-direct-image.proof.md, paragraph (2);
parent node step 3; Stacks 09BP, lemma-j-shriek-limits, and 0941.
(blueprint: lem-sp-compactification-open-limit). -/
theorem compactificationOpenLimit {X Z : Scheme.{u}} (j : X ⟶ Z)
    [IsOpenImmersion j] [QuasiCompact j] :
    IsIso (openLimit l E j) ∧
    ∀ (K : DerivedCategory (Fixed l E X)) (n : ℕ),
      (openLimit l E j).app K ≫
          (coefficientConstantTowerProjection l E Z n).app
            (((fixedOpenOrd l E j).mapDerivedCategory).obj K) =
        (openOrd l E j).mapDerivedCategory.map
          ((coefficientConstantTowerProjection l E X n).app K) ≫
            (fixedOpenEvaluation l E j n).inv.app K := by
  constructor
  · exact cbcRealizationLimitMap_isIso (openOrd l E j)
      (endpointOpenProducts j ((PurCompactSupport.completed l E).ring Z)
        ((PurCompactSupport.completed l E).ring X) ((PurCompactSupport.completed l E).pull j))
  · intro K n
    have h := mate_limit_projection
      ((Functor.const ℕᵒᵖ : scalarReductionSource l E X ⥤ _).mapDerivedCategory)
      ((Functor.const ℕᵒᵖ : scalarReductionSource l E Z ⥤ _).mapDerivedCategory)
      (coefficientConstantTowerLimit l E X) (coefficientConstantTowerLimit l E Z)
      (cbcRealizationLimitAdj X ((PurCompactSupport.completed l E).ring X))
      (cbcRealizationLimitAdj Z ((PurCompactSupport.completed l E).ring Z))
      (openOrd l E j).mapDerivedCategory (fixedOpenOrd l E j).mapDerivedCategory
      (coefficientConstantTowerEvaluation l E X n)
      (coefficientConstantTowerEvaluation l E Z n)
      (constantEvaluationIso (scalarReductionSource l E X) (op n))
      (constantEvaluationIso (scalarReductionSource l E Z) (op n))
      (cbcRealizationConst (openOrd l E j)).hom (fixedOpenEvaluation l E j n)
      (open_constant_evaluation l E j n) K
    have h' : (openLimit l E j).app K ≫
        (counitProjection l E Z n).app _ ≫ (fixedOpenEvaluation l E j n).hom.app K =
        (openOrd l E j).mapDerivedCategory.map ((counitProjection l E X n).app K) := by
      dsimp only [counitProjection]
      convert! h using 1
      simp only [Category.assoc]
      rfl
    rw [counitProjection_eq, counitProjection_eq] at h'
    apply (cancel_mono ((fixedOpenEvaluation l E j n).hom.app K)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    exact h'.trans (Category.comp_id _).symm

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
