/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CondensedTateIntegralTowerData

/-! Fixed-pair reduction of the normalized Tate tensor square.

Source: smooth-purity transport, normalized Tate tower, Step 4.
(blueprint: lem-pur-tate-tensor-normalized-square-pair)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Etale.FiniteSmoothPurity
namespace AlgebraicGeometry.Scheme.PurityIntegralTower

def normalizedAt
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (e : ∀ n : ℕ, M.level n ≅ (derivedRealization T ell n).obj (finiteTwist T ell n d))
    (h : M.tower = strictDerivedTower T ell d) (n : ℕ)
    (c : (realization T ell n).obj (finiteSheaf T ell n d) ≅ quotientLine T ell n d) : Prop :=
  ProjectionBalanced T ell n d c ∧
    (pbcDerivedRestrict (pbcAdicProjection T (datum.{u} ell) n)).map
        ((finiteModelIso T ell hT n d).inv ≫ (e n).inv) ≫ (M.evaluation n).hom ≫
        (pbcTowerEvaluation T (pbcAdicCompletion T (datum.{u} ell)) n).map (eqToHom h) =
      (Functor.mapDerivedCategorySingleFunctor
        (pbcRestrict (pbcAdicProjection T (datum.{u} ell) n))
        (-(2 * (d : ℤ)))).hom.app _ ≫
      (_root_.DerivedCategory.singleFunctor _ (-(2 * (d : ℤ)))).map
        ((pbcRestrict (pbcAdicProjection T (datum.{u} ell) n)).map c.hom) ≫
      (Functor.mapDerivedCategorySingleFunctor
        ((CategoryTheory.evaluation ℕᵒᵖ
          (pbcModules T (pbcAdicCompletion T (datum.{u} ell)))).obj (op n))
        (-(2 * (d : ℤ)))).inv.app (strictTower T ell d)

/-- The finite scalar square for one fixed pair, assuming the two selected
projection-normalized models. This is the local tensor and mate calculation;
the all-level theorem only supplies these two models from `ProjectionNormalized`.

Source: smooth-purity transport, normalized Tate tower, Step 4.
(blueprint: lem-pur-tate-tensor-normalized-square-pair)

Proof: evaluate the two maps on the selected ordinary root-tensor models. The
`ProjectionBalanced` equations identify scalar extension followed by the finite
root comparison with quotient tensor balancing. The two `normalizedAt` equations
transport these ordinary formulas through exact single/evaluation comparisons.
The scalar adjunction mate and the strict tower transition then identify the
result with `M.normalization`; generator equality extends by sheafification.
Equal indices, zero tensor powers, and empty schemes use the same unit formulas. -/
theorem tateTensor_normalizedSquare_of_pair
    (T : Scheme.{u}) [IsNoetherian T] (ell : ℕ) [Fact ell.Prime]
    (hT : IsUnit (ell : Γ(T, ⊤))) (d : ℕ)
    (M : AdicTower T (datum.{u} ell))
    (e : ∀ n : ℕ, M.level n ≅ (derivedRealization T ell n).obj (finiteTwist T ell n d))
    (h : M.tower = strictDerivedTower T ell d)
    (b a : ℕ) (hab : a ≤ b)
    (cb : (realization T ell b).obj (finiteSheaf T ell b d) ≅ quotientLine T ell b d)
    (ca : (realization T ell a).obj (finiteSheaf T ell a d) ≅ quotientLine T ell a d)
    (hb : normalizedAt T ell hT d M e h b cb)
    (ha : normalizedAt T ell hT d M e h a ca)
    (r : CoefficientLineComparison
      (FiniteReduction.quotient.{u} ell (Nat.add_le_add_right hab 1))
      (ell ^ (b + 1)) (ell ^ (a + 1))
      (CharP.cast_eq_zero _ _) (CharP.cast_eq_zero _ _) T) :
    (pbcDerivedExtend (pbcAdicQuotient T (datum.{u} ell) b a hab)).map (e b).hom ≫
        (scalarComparison T ell b a hab).hom.app (finiteTwist T ell b d) ≫
        (derivedRealization T ell a).map (proTwistMap d r) =
      (M.normalization b a hab).hom ≫ (e a).hom := by sorry

end AlgebraicGeometry.Scheme.PurityIntegralTower
