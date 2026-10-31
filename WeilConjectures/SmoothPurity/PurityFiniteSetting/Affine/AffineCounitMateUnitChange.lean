/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows

/-! # Unit conversion for the ordered affine counit mate

The coefficient-unit and monoidal-unit presentations are related by naturality
of the same exceptional adjunction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Etale.affineLinearCompactComparison
  Etale.affineLinearCoefficientDescent Etale.vectorIntegrationBaseCoefficientPullback

private theorem homEquiv_comp_unit
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {J K : C} {U V W : D} (b : J ⟶ K)
    (f : L.obj K ⟶ U) (g : U ⟶ V) (u : V ⟶ W) :
    (b ≫ adj.homEquiv K V (f ≫ g)) ≫ R.map u =
      b ≫ adj.homEquiv K W (f ≫ g ≫ u) := by
  rw [Category.assoc, ← Adjunction.homEquiv_naturality_right, Category.assoc]

/-- Converting the actual finite coefficient-unit affine mate to the monoidal
unit gives the prescribed ordered tower counit transpose.
Source: the two counit-mate definitions and naturality of the exceptional
adjunction, in smooth-purity Agreement on the model.
(blueprint: lem-pur-affine-counit-mate-unit-change).

Proof: expand the affine mate, unitChange and towerAdjoint. Naturality of the
adjunction Hom equivalence in its right argument moves the coefficient-unit
comparison inside the transpose. Associativity identifies the resulting counit
composite with towerAdjoint. The ordered coefficient descent is unchanged.
This is a categorical identity, so rank zero, empty schemes and zero rings
require no separate assumptions. -/
theorem affineCounitMate_unitChange (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))),
      Etale.OrdinaryFiniteP1Datum P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t T hT)
    (Y : Scheme.{u}) [IsNoetherian Y]
    (hY : IsUnit (P.diagonalExponent : Γ(Y, ⊤))) (d : ℕ) :
    P.diagonalAffineMate t D Y hY d ≫
        (OrientationCounit.unitChange P (affineTraceProjection Y d)).inv =
      ((Etale.affineLinearCoefficientDescent P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates t Y hY d) ≪≫
        Etale.vectorIntegrationBaseCoefficientPullback P.Coefficient P.diagonalExponent
          P.diagonalExponent_annihilates t (affineTraceProjection Y d) hY d).inv ≫
        Etale.CoordinateCounitArrows.towerAdjoint P.diagonalExponent
          (pow_pos P.coefficients.prime.out.pos P.level) P.Coefficient
          P.diagonalExponent_annihilates t D Y hY d := by
  unfold diagonalAffineMate OrientationCounit.unitChange
    Etale.CoordinateCounitArrows.towerAdjoint
  exact homEquiv_comp_unit _ _ _ _ _

end WeilConjectures.PurityFiniteSetting
