/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ChernFlagFormula
import Mathlib.CategoryTheory.Linear.FunctorCategory
public import WeilConjectures.AlgebraicGeometry.KummerAdditivity
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
public import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
public import WeilConjectures.SmoothPurity.OrdinaryFiniteTwistTransportUniqueness
public import WeilConjectures.SmoothPurity.ProjectiveBundleFormula
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityChernEtaleOrigin
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting

/-!
# Coefficients of the ordered Chern-root product

Source: Stacks Project, Tag 0FI5, coefficient expansion of the splitting-principle product.
(blueprint: lem-pur-flag-product-coefficient-algebra).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory AlgebraicGeometry

namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u}) (S : Scheme.{u})

/-- The root multiplication operator is additive, hence kills zero. -/
theorem ordinaryFiniteHyperplaneStep_zero
    (x : Etale.ordinaryFiniteUnit P.Coefficient S ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧) (i : ℕ) :
    P.ordinaryFiniteHyperplaneStep S x i 0 = 0 := by
  simp [ordinaryFiniteHyperplaneStep, ordinaryFiniteHyperplaneStepRaw,
    ProEtale.derivedTensor]

/-- The ordered cup step is additive in the arbitrary pro-etale input class.
Source: Stacks Tag 0FI5, bilinear full-support cup product.
Proof: tensoring is additive in its first variable, then distribute composition.
(blueprint: lem-pur-chern-coefficient-assembly). -/
theorem ordinaryFiniteHyperplaneStep_add (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧)
    (i : ℕ) (α β : ordinaryFiniteCohomology P T i) :
    P.ordinaryFiniteHyperplaneStep T h i (α + β) =
      P.ordinaryFiniteHyperplaneStep T h i α + P.ordinaryFiniteHyperplaneStep T h i β := by
  unfold ordinaryFiniteHyperplaneStep ordinaryFiniteHyperplaneStepRaw
  dsimp only [ProEtale.derivedTensor]
  rw [Functor.map_add]
  simp only [NatTrans.app_add, Preadditive.add_comp, Preadditive.comp_add]

private theorem coeff_zero (r : ℕ)
    (x : Fin r → (Etale.ordinaryFiniteUnit P.Coefficient S ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧)) :
    P.ordinaryFiniteFlagProductCoefficient S r x 0 = P.ordinaryFiniteCohomologyOne S := by
  cases r <;> rfl

/-- The product of r linear factors has no coefficient above degree r. -/
theorem ordinaryFiniteFlagProductCoefficient_above (r : ℕ)
    (x : Fin r → (Etale.ordinaryFiniteUnit P.Coefficient S ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧)) (i : ℕ) (hi : r < i) :
    P.ordinaryFiniteFlagProductCoefficient S r x i = 0 := by
  induction r generalizing i with
  | zero => cases i with
    | zero => omega
    | succ i => rfl
  | succ r ih =>
    cases i with
    | zero => omega
    | succ i =>
      rw [ordinaryFiniteFlagProductCoefficient, ih _ _ (by omega),
        ih _ _ (by omega), ordinaryFiniteHyperplaneStep_zero, add_zero]

/-- Its top coefficient is the ordered product, including the empty product. -/
theorem ordinaryFiniteFlagProductCoefficient_top (r : ℕ)
    (x : Fin r → (Etale.ordinaryFiniteUnit P.Coefficient S ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧)) :
    P.ordinaryFiniteFlagProductCoefficient S r x r =
      P.ordinaryFiniteFlagTopProduct S r x := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [ordinaryFiniteFlagProductCoefficient,
      ordinaryFiniteFlagProductCoefficient_above P S r _ (r + 1) (by omega),
      zero_add, ih, ordinaryFiniteFlagTopProduct]

/-- Prepending a root has the expected coefficient recurrence whenever right
multiplication by the roots commutes. The proof expands the last-factor recurrence,
uses additivity, commutes the two last multiplication operators, and rearranges sums. -/
theorem ordinaryFiniteFlagProductCoefficient_prepend
    (hc : ∀ (x y : Etale.ordinaryFiniteUnit P.Coefficient S ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧) (i : ℕ)
      (α : P.ordinaryFiniteCohomology S i),
      P.ordinaryFiniteHyperplaneStep S y (i + 1)
        (P.ordinaryFiniteHyperplaneStep S x i α) =
      P.ordinaryFiniteHyperplaneStep S x (i + 1)
        (P.ordinaryFiniteHyperplaneStep S y i α))
    (r : ℕ)
    (x : Fin (r + 1) → (Etale.ordinaryFiniteUnit P.Coefficient S ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates S)⟦(2 : ℤ)⟧)) (i : ℕ) :
    P.ordinaryFiniteFlagProductCoefficient S (r + 1) x (i + 1) =
      P.ordinaryFiniteFlagProductCoefficient S r (fun j ↦ x j.succ) (i + 1) +
      P.ordinaryFiniteHyperplaneStep S (x 0) i
        (P.ordinaryFiniteFlagProductCoefficient S r (fun j ↦ x j.succ) i) := by
  induction r generalizing i with
  | zero =>
    cases i <;>
      simp [ordinaryFiniteFlagProductCoefficient, ordinaryFiniteHyperplaneStep_zero]
  | succ r ih =>
    cases i with
    | zero =>
      have hy := ih (fun j ↦ x j.castSucc) 0
      have hz : P.ordinaryFiniteFlagProductCoefficient S (r + 1)
          (fun j ↦ x j.succ) 1 =
          P.ordinaryFiniteFlagProductCoefficient S r (fun j ↦ x j.castSucc.succ) 1 +
          P.ordinaryFiniteHyperplaneStep S (x (Fin.last (r + 1))) 0
            (P.ordinaryFiniteCohomologyOne S) := by
        rw [ordinaryFiniteFlagProductCoefficient, coeff_zero]
        rfl
      change P.ordinaryFiniteFlagProductCoefficient S (r + 1)
          (fun j ↦ x j.castSucc) 1 +
          P.ordinaryFiniteHyperplaneStep S (x (Fin.last (r + 1))) 0
            (P.ordinaryFiniteCohomologyOne S) = _
      rw [hy, hz]
      simp only [coeff_zero, Fin.succ_castSucc]
      ac_rfl
    | succ i =>
      rw [ordinaryFiniteFlagProductCoefficient, ih, ih]
      simp only [ordinaryFiniteHyperplaneStep_add]
      rw [hc]
      simp only [ordinaryFiniteFlagProductCoefficient, ordinaryFiniteHyperplaneStep_add]
      ac_rfl

end WeilConjectures.PurityFiniteSetting
