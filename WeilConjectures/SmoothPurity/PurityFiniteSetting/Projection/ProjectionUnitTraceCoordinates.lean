/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Projection.ProjectionUnitIntegration

/-! # The ordinary trace behind the independent unit integration

Source: the unit-mate step of projection purity agreement.
(blueprint: lem-pur-projection-unit-trace-coordinates)
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures.PurityFiniteSetting
open ProEtale ProEtale.AffineSpacePurity

/-- The ordinary trace at the diagonal exponent, transported from the ordered
tower coefficient to its coefficient on the total affine space.
Source: the defining affine unit mate in projection purity agreement.
(blueprint: lem-pur-projection-unit-trace-coordinates) -/
def projectionUnitTraceRaw (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) :=
  letI := isNoetherian_of_locallyOfFiniteType aY
  letI := affineTraceNoetherian Y d
  let hN := pow_pos P.coefficients.prime.out.pos P.level
  let t := Etale.projectiveLineTraceTransport P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates
  let D := Etale.projectiveLineTraceDatum P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates
  let e := Etale.affineLinearCoefficientDescent P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t Y (P.diagonalExponent_isUnit aY) d ≪≫
      Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t (affineTraceProjection Y d)
          (P.diagonalExponent_isUnit aY) d
  (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
    (affineTraceProjection Y d)).map e.inv ≫
  (Etale.affineLinearCompactComparison P.diagonalExponent hN P.Coefficient
    P.diagonalExponent_annihilates Y (P.diagonalExponent_isUnit aY) d).inv ≫
  Etale.affineTraceCounit P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t D Y (P.diagonalExponent_isUnit aY) d

/-- The independently defined unit integration is the comparison of the ordinary
adjunct of the actual trace at the diagonal exponent. The heterogeneous equation
fixes that trace in the original recursive affine-tower coordinates.

Source: the unit-mate step of
blueprint, sec-smooth-purity/sk-thm-smooth-purity,
`lem-pur-projection-purity-agreement.proof.md`.
(blueprint: lem-pur-projection-unit-trace-coordinates)

Proof: the definition of diagonalAffineMate is coefficient descent followed by
the ordinary adjunct of the ordered counit. Naturality of the adjunction Hom
bijection in the source combines coefficient descent into the trace. Apply
the exact comparison functor and the inverse dualizing comparison. Induct on
the number of affine lines to identify the dependent scheme/projection pairs
of the two recursive models. Transport the ordinary trace along this equality;
the comparison of its adjunct transports with it. The HEq specification of
projectionUnitIntegration then identifies the resulting pro-etale arrow.
This includes rank zero, since both tower pairs then are (Y,id). -/
theorem projectionUnitIntegration_trace
    (P : PurityFiniteSetting.{u}) (Y : Scheme.{u})
    (aY : Y ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aY] [QuasiCompact aY]
    (d : ℕ) :
    letI := (projection_geometry Y d).2
    ∃ t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient)
      (iteratedAffineLineProj Y d)).obj
        (P.diagonalTwistEtale (iteratedAffineLine Y d) d) ⟶
          Etale.ordinaryFiniteUnit P.Coefficient Y,
      HEq t (projectionUnitTraceRaw P Y aY d) ∧
      projectionUnitIntegration P Y aY d =
        (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
          (iteratedAffineLine Y d)).mapDerivedCategory.map
            ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient
              (iteratedAffineLineProj Y d)).homEquiv _ _ t) ≫
          (P.diagonalDualizingComparison (iteratedAffineLineProj Y d)).inv := by
  let := isNoetherian_of_locallyOfFiniteType aY
  let := affineTraceNoetherian Y d
  let := (projection_geometry Y d).2
  have hp : (⟨affineTraceTower Y d, affineTraceProjection Y d⟩ :
      Σ X : Scheme.{u}, X ⟶ Y) =
      ⟨iteratedAffineLine Y d, iteratedAffineLineProj Y d⟩ := by
    induction d with
    | zero => rfl
    | succ d ih =>
      exact congrArg (fun q : Σ X : Scheme.{u}, X ⟶ Y ↦
        (⟨AffineSpace PUnit.{u + 1} q.1,
          (AffineSpace PUnit.{u + 1} q.1 ↘ q.1) ≫ q.2⟩ :
            Σ X : Scheme.{u}, X ⟶ Y)) ih
  have hn : projectionUnitIntegrationRaw P Y aY d =
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient)
        (affineTraceTower Y d)).mapDerivedCategory.map
          ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient
            (affineTraceProjection Y d)).homEquiv _ _
              (projectionUnitTraceRaw P Y aY d)) ≫
        (P.diagonalDualizingComparison (affineTraceProjection Y d)).inv := by
    dsimp only [projectionUnitIntegrationRaw, diagonalAffineMate, projectionUnitTraceRaw]
    rw [Adjunction.homEquiv_naturality_left]
    rfl
  have transport (X X' : Scheme.{u}) (f : X ⟶ Y) (g : X' ⟶ Y)
      [HasCompactification f] [HasCompactification g]
      (h : (⟨X, f⟩ : Σ X : Scheme.{u}, X ⟶ Y) = ⟨X', g⟩)
      (t : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) f).obj
        (P.diagonalTwistEtale X d) ⟶ Etale.ordinaryFiniteUnit P.Coefficient Y) :
      ∃ t' : (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) g).obj
        (P.diagonalTwistEtale X' d) ⟶ Etale.ordinaryFiniteUnit P.Coefficient Y,
        HEq t' t ∧
        HEq ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} P.Coefficient) X').mapDerivedCategory.map
            ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient g).homEquiv _ _ t') ≫
              (P.diagonalDualizingComparison g).inv)
          ((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} P.Coefficient) X).mapDerivedCategory.map
              ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient f).homEquiv _ _ t) ≫
                (P.diagonalDualizingComparison f).inv) := by
    cases h
    exact ⟨t, HEq.rfl, HEq.rfl⟩
  obtain ⟨t, ht, he⟩ := transport _ _ (affineTraceProjection Y d)
    (iteratedAffineLineProj Y d) hp (projectionUnitTraceRaw P Y aY d)
  refine ⟨t, ht, ?_⟩
  have hz := (projectionUnitIntegration_existsUnique P Y aY d).exists.choose_spec
  exact eq_of_heq (hz.trans ((heq_of_eq hn).trans he.symm))

end WeilConjectures.PurityFiniteSetting
