/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurStrictScalar.StrictScalarFiniteEvaluationTransport

/-! # Finite normalization of native ramified reduction

Source: Stacks 03EK, 06YY and 0940.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Evaluation of native reduction at a specified positive quotient exponent.
Source: Stacks 0940 (blueprint: def-pur-positive-reduction-evaluation). -/
def positiveReductionEvaluation (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W) (m : ℕ) (hm : 1 ≤ m) :
    reduction l E W S ⋙
        ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) W (m - 1) ≅
      pbcDerivedExtend (PurCompactSupport.projection l E m hm W) ⋙
        positiveRestriction l E W m hm :=
  match m, hm with
  | 0, h => False.elim (Nat.not_succ_le_zero 0 h)
  | n + 1, _ => reductionEvaluation l E W S n

variable (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

/-- Local ramified quotient balancing commutes with the prescribed finite evaluation.
Source: Stacks 03EK, 06YY, 0940; local part of the ramified image argument.
(blueprint: lem-pur-ramified-reduction-finite-evaluation).
Proof: evaluate the whole-cochain counit equation for reductionBalancing on a K-flat
representative. Its ordinary balancing and finiteOrdinaryBalancing agree on the
quotient generators b tensor (1 tensor x). The strict quotient-unit presentation
of both reduction calculi identifies their evaluated counits with the ordinary
quotient maps. The normalized derived tensorSquare reassociates successive scalar
extensions with the same unit. Cancel the computing counits, which are invertible
on K-flat representatives, and descend using naturality and a K-flat resolution.
This is a local coefficient equation: no geometric direct image occurs. -/
theorem ramifiedReduction_finiteEvaluation (W : Scheme.{u})
    (S : CoefficientDerivedSystemCalculus.{u, u} l E W)
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F W) (e : ℕ)
    (he : PurCompactSupport.Ramification l E F i e) (hepos : 1 ≤ e)
    (M : DerivedCategory (scalarReductionSource l E W)) (n : ℕ) :
    (ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) W n).map
        ((reductionBalancing l E F i W S S' e he hepos).hom.app M) ≫
      (subsequenceEvaluation l F W e n).hom.app
        ((reduction l F W S').obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i W)).obj M)) ≫
      (positiveReductionEvaluation l F W S' (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n))).hom.app
          ((pbcDerivedExtend (completedCoefficientMap l E F i W)).obj M) ≫
      (positiveRestriction l F W (e * (n + 1))
        (Nat.mul_pos hepos (Nat.le_add_left 1 n))).map
          ((PurCompactSupport.tensorSquare (completedCoefficientMap l E F i W)
            ((PurCompactSupport.finiteChange l E F i e he hepos (n + 1)
              (Nat.le_add_left 1 n)).map W)
            (PurCompactSupport.projection l E (n + 1) (Nat.le_add_left 1 n) W)
            (PurCompactSupport.projection l F (e * (n + 1))
              (Nat.mul_pos hepos (Nat.le_add_left 1 n)) W)
            (PurCompactSupport.ramified_reduction_square l E F i e he hepos (n + 1)
              (Nat.le_add_left 1 n) W)).hom.app M) =
      (tensorEvaluation l E F i W n).hom.app ((reduction l E W S).obj M) ≫
        (baseTensor l E F i W).map ((reductionEvaluation l E W S n).hom.app M) ≫
        (finiteBalancing l E F i W e he hepos n).hom.app
          ((pbcDerivedExtend (PurCompactSupport.projection l E (n + 1)
            (Nat.le_add_left 1 n) W)).obj M) := by sorry

end WeilConjectures.PurStrictScalar
