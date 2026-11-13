/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ScalarExtensionTower.ScalarExtensionTowerRealizationData
public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTowerRealizations
import all WeilConjectures.SmoothPurity.Coefficient.CoefficientEvaluationTensorNaturality
import WeilConjectures.SmoothPurity.Supporting.NaturalCoherentTensorLevel
import all WeilConjectures.TraceFormula.Coherent.CoherentQuotientOrdinaryLift

/-! # Homogeneous generators of the transported strict quotient tensor tower

Source: Stacks 03EL, 07A4 and 0941; step 3 of
stage3-pur-scalar-tensor-model-normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace WeilConjectures.ScalarExtensionTower

attribute [local irreducible] HasDerivedCategory.standard SheafOfModules.monoidalCategory
  constantSheaf completedIntegralCommRingSheafUnrestricted coefficientSequenceCommRingSheaf

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

set_option trace.profiler true in
/-- Tensoring strict quotient identifications gives the specified generator formula.
Source: Stacks 03EL, 07A4 and 0941; step 3 of
stage3-pur-scalar-tensor-model-normalization.
(blueprint: lem-pur-strict-quotient-tensor-generator).

Proof: evaluate the restricted tensor of the inverse isomorphisms a,b at level n.
Naturality of restriction/evaluation and the normalized tensor evaluation comparison
identifies its composite with the reference tower comparison with the finite total
tensor of kappaC,kappaD. This uses the two displayed evaluation equations and cancels
the reference evaluation isomorphisms. The tensor evaluation comparison carries a
homogeneous generator to the tensor of its evaluated sections. A total tensor map
applies its two component chain maps to these sections. Scalar restriction leaves
the section unchanged. These three equations give the displayed formula. The maps
are already strict tower maps; no new transition compatibility or derived
faithfulness is asserted. All total degrees and the zero and first-quotient cases
are included. -/
theorem strictQuotientTensorGenerator (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules.{u, u} l E W) ℤ)
    (C D : Complex l E W)
    (a : (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj P) ≅ C)
    (b : (((pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)).obj Q) ≅ D)
    (κC : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj P)
    (κD : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ≅
        (unrestrictedIntegralFiniteComplex l E W n).obj Q)
    (ha : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
        κC n = ((pullbackTensorReductionEvaluationComplex l E W n).app P).symm)
    (hb : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).mapIso b ≪≫
        κD n = ((pullbackTensorReductionEvaluationComplex l E W n).app Q).symm) :
    let F := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    let q := F.mapIso ((tensor l E W).mapIso (a.symm.prod b.symm)) ≪≫
      pullbackTensorTensorTower l E W P Q
    ∀ (n : ℕ) (p r : ℤ) (U : W.ProEtᵒᵖ)
      (x : (C.X p).val.obj (op (n, U.unop)))
      (y : (D.X r).val.obj (op (n, U.unop))),
      ((q.hom.app (op n)).f (p + r)).val.app U
        (integralComparisonRestrictedSection l E W
          (((tensor l E W).obj (C, D)).X (p + r)) n U
          (generator l E W C D p r (op (n, U.unop)) x y)) =
        integralTensorGenerator l E W P Q n p r U
          (((κC n).hom.f p).val.app U
            (coefficientEvaluationSection l E W (C.X p) n U x))
          (((κD n).hom.f r).val.app U
            (coefficientEvaluationSection l E W (D.X r) n U y)) := by
  dsimp only
  intro n p r V x y
  let R := (pullbackTensorOrdinaryReduction l E W).mapHomologicalComplex (.up ℤ)
  let ev := (coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)
  let res := (scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)
  let U := (coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ) ⋙
    HomologicalComplex.complexOfFunctorsToFunctorToComplex
  let B := coefficientTotalTensor.{u, u + 1, u} (Scheme.ProEt.topology W)
    (integralCoefficientCommRingSheaf l E W n)
  let c := (tensor l E W).mapIso (a.symm.prod b.symm)
  have hκa : ev.map a.inv ≫ (pullbackTensorReductionEvaluationComplex l E W n).inv.app P =
      (κC n).hom := by
    have h := congrArg Iso.hom (ha n)
    change ev.map a.hom ≫ (κC n).hom =
      (pullbackTensorReductionEvaluationComplex l E W n).inv.app P at h
    rw [← h, ← Category.assoc, ← ev.map_comp, a.inv_hom_id, ev.map_id, Category.id_comp]
  have hκb : ev.map b.inv ≫ (pullbackTensorReductionEvaluationComplex l E W n).inv.app Q =
      (κD n).hom := by
    have h := congrArg Iso.hom (hb n)
    change ev.map b.hom ≫ (κD n).hom =
      (pullbackTensorReductionEvaluationComplex l E W n).inv.app Q at h
    rw [← h, ← Category.assoc, ← ev.map_comp, b.inv_hom_id, ev.map_id, Category.id_comp]
  have hlevel : (U.map c.hom).app (op n) ≫
      (pullbackTensorTensorTower l E W P Q).hom.app (op n) =
    (pullbackTensorRestrictedLevel l E W ((tensor l E W).obj (C, D)) n).hom ≫
      res.map ((coefficientEvaluationTensorIso l E W n C D).hom ≫
        B.map (Prod.mkHom (κC n).hom (κD n).hom)) := by
    have htw := (pullbackTensorTensorTower_existsUnique l E W P Q).exists.choose_spec n
    change (pullbackTensorTensorTower l E W P Q).app (op n) = _ at htw
    rw [← Iso.app_hom, htw]
    unfold pullbackTensorTensorTowerLevel
    change (U.map c.hom).app (op n) ≫
      ((pullbackTensorRestrictedLevel l E W ((tensor l E W).obj (R.obj P, R.obj Q)) n).hom ≫
        res.map (coefficientEvaluationTensorIso l E W n (R.obj P) (R.obj Q)).hom ≫
        res.map (B.map (Prod.mkHom
          ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
          ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q)))) = _
    have hn := (pullbackTensorRestrictionEvaluation l E W n).hom.naturality c.hom
    change (U.map c.hom).app (op n) ≫
        (pullbackTensorRestrictedLevel l E W ((tensor l E W).obj (R.obj P, R.obj Q)) n).hom =
      (pullbackTensorRestrictedLevel l E W ((tensor l E W).obj (C, D)) n).hom ≫
        res.map (ev.map c.hom) at hn
    rw [← Category.assoc, hn]
    simp only [Category.assoc, ← res.map_comp]
    have he := pullbackTensorEvaluationTensor_naturality l E W n a.inv b.inv
    change ev.map c.hom ≫
        (coefficientEvaluationTensorIso l E W n (R.obj P) (R.obj Q)).hom =
      (coefficientEvaluationTensorIso l E W n C D).hom ≫
        B.map (Prod.mkHom (ev.map a.inv) (ev.map b.inv)) at he
    rw [← Category.assoc, he]
    simp only [Category.assoc]
    rw [← B.map_comp]
    have hp : Prod.mkHom (ev.map a.inv) (ev.map b.inv) ≫
        Prod.mkHom ((pullbackTensorReductionEvaluationComplex l E W n).inv.app P)
          ((pullbackTensorReductionEvaluationComplex l E W n).inv.app Q) =
      Prod.mkHom (κC n).hom (κD n).hom := by
      exact Prod.ext hκa hκb
    rw [hp]
  have hsection (K : Complex l E W) (i : ℤ)
      (z : (K.X i).val.obj (op (n, V.unop))) :
    (((pullbackTensorRestrictedLevel l E W K n).hom).f i).val.app V
      (integralComparisonRestrictedSection l E W (K.X i) n V z) =
      coefficientEvaluationSection l E W (K.X i) n V z := by
    change (((eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom.app
      (K.X i)).val.app V) _ = _
    exact (restrictionEvaluation_apply l E W (K.X i) n V z).trans rfl
  change (((U.map c.hom).app (op n) ≫
      (pullbackTensorTensorTower l E W P Q).hom.app (op n)).f (p + r)).val.app V _ = _
  rw [hlevel]
  change ((B.map (Prod.mkHom (κC n).hom (κD n).hom)).f (p + r)).val.app V
    (((coefficientEvaluationTensorIso l E W n C D).hom.f (p + r)).val.app V
      ((((pullbackTensorRestrictedLevel l E W ((tensor l E W).obj (C, D)) n).hom).f
        (p + r)).val.app V _)) = _
  rw [hsection ((tensor l E W).obj (C, D)) (p + r)
    (generator l E W C D p r (op (n, V.unop)) x y)]
  erw [pullbackTensorEvaluationTensor_generator_cast l E W n C D p r (p + r) rfl V x y]
  erw [CategoryTheory.ScalarHomTensor.tensor_generator_map.{u + 1, u, u}]
  rfl

end WeilConjectures.ScalarExtensionTower
