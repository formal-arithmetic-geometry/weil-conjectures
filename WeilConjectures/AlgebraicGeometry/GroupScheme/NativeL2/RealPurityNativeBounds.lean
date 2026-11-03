/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import WeilConjectures.PointCount

/-! # Combining the two exterior-power bounds

Source: sk-p-real-purity, dual paragraph: the bounds for alpha and alpha inverse
force the required absolute value (blueprint: lem-rp-native-purity-of-two-bounds).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.NativeL2
open NativeCondensedModule

private theorem norm_eq_of_sq_bounds {q w : ℝ} {a : ℂ}
    (hq : 0 < q) (ha : a ≠ 0)
    (hupper : ‖a‖ ^ 2 ≤ q ^ w) (hinverse : ‖a⁻¹‖ ^ 2 ≤ q ^ (-w)) :
    ‖a‖ = q ^ (w / 2) := by
  have hp : 0 < q ^ w := Real.rpow_pos_of_pos hq _
  have ha' : 0 < ‖a‖ ^ 2 := pow_pos (norm_pos_iff.mpr ha) _
  rw [norm_inv, inv_pow, Real.rpow_neg hq.le] at hinverse
  have hlower : q ^ w ≤ ‖a‖ ^ 2 := (inv_le_inv₀ ha' hp).mp hinverse
  have heq : ‖a‖ ^ 2 = q ^ w := le_antisymm hupper hlower
  have hsq : (q ^ (w / 2)) ^ 2 = q ^ w := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    congr 1
    ring
  nlinarith [Real.rpow_pos_of_pos hq (w / 2), norm_nonneg a]

/-- Cancelling a positive determinant norm in the Rankin upper estimate.
Source: sk-p-real-purity, determinant cancellation in step 4
(blueprint: lem-rp-native-purity-of-two-bounds).

Proof: expand the real power of a sum and cancel the positive factor q^B. -/
theorem square_bound_of_scaled_bound {q a B w : ℝ} (hq : 0 < q)
    (h : a * q ^ B ≤ q ^ (B + w)) : a ≤ q ^ w := by
  rw [Real.rpow_add hq] at h
  exact (mul_le_mul_iff_right₀ (Real.rpow_pos_of_pos hq B)).mp
    (by simpa only [mul_comm] using h)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (X₀ : Over (Spec (.of D.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]

/-- Every eigenvalue of the native local Frobenius is nonzero, because its defining
semilinear return transport is an isomorphism.
Source: sk-p-real-purity, inverse-eigenvalue paragraph
(blueprint: lem-rp-native-purity-of-two-bounds).

Proof: a zero eigenvalue would give a nonzero vector killed by the transport
isomorphism. Apply its injectivity to that vector and zero. -/
theorem closedOperator_eigenvalue_ne_zero (M : WeilModule D l X₀)
    (x : {x : X₀.left // x ∈ closedPoints X₀.left})
    (i : X₀.left.residueField x.val →+* D.k)
    (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
    (α : ULift.{u + 1} (PadicAlgCl l))
    (hα : Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α) :
    α ≠ 0 := by
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  intro hz
  have heq := hv.apply_eq_smul
  rw [hz, zero_smul] at heq
  apply hv.2
  let e := transport l D (D.geometricFrobenius X₀).hom M.carrier M.str
    (localClosedPoint D X₀ x i hi) (localClosedPoint D X₀ x i hi)
    (localClosedPointDegree D X₀ x - 1) (localClosedPoint_return D X₀ x i hi)
  apply e.toLinearEquiv.injective
  change e.hom.hom v = e.hom.hom 0
  simpa only [closedOperator, operator, e, map_zero] using heq

/-- The upper exterior-power bound for a constituent and the corresponding upper bound
for its inverse eigenvalues imply native punctual purity.
Source: sk-p-real-purity, dual paragraph
(blueprint: lem-rp-native-purity-of-two-bounds).

Proof: closed residue fields are finite and nonempty, so their cardinalities are positive.
Local Frobenius is invertible, so the embedded eigenvalue is nonzero. The inverse bound
therefore reverses to the lower bound for its squared norm. The two squared bounds give
equality, and the positive square root gives q_x^(w/2), at every closed point and lift. -/
theorem pure_of_upper_and_inverse_bounds
    (M : WeilModule D l X₀) (iota : PadicAlgCl l →+* ℂ) (w : ℝ)
    (hupper : ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
      (i : X₀.left.residueField x.val →+* D.k)
      (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
      (α : ULift.{u + 1} (PadicAlgCl l)),
      Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
        ‖iota α.down‖ ^ 2 ≤ (Nat.card (X₀.left.residueField x.val) : ℝ) ^ w)
    (hinverse : ∀ (x : {x : X₀.left // x ∈ closedPoints X₀.left})
      (i : X₀.left.residueField x.val →+* D.k)
      (hi : i.comp (X₀.hom.residueFieldAlgebraMap x.val) = algebraMap D.k₀ D.k)
      (α : ULift.{u + 1} (PadicAlgCl l)),
      Module.End.HasEigenvalue (closedOperator D l X₀ M x i hi).hom α →
        ‖iota (α.down)⁻¹‖ ^ 2 ≤ (Nat.card (X₀.left.residueField x.val) : ℝ) ^ (-w)) :
    Pure D l X₀ M iota w := by
  intro x i hi α hα
  let := (X₀.hom.residueFieldAlgebraMap x.val).toAlgebra
  have := X₀.hom.finite_residueField_of_isClosed x.val x.property
  have : Finite (X₀.left.residueField x.val) := Module.finite_of_finite D.k₀
  have hq : (0 : ℝ) < Nat.card (X₀.left.residueField x.val) := by
    exact_mod_cast Nat.card_pos
  have ha : α.down ≠ 0 := by
    intro hz
    exact closedOperator_eigenvalue_ne_zero D l X₀ M x i hi α hα (ULift.ext _ _ hz)
  apply norm_eq_of_sq_bounds hq ((map_ne_zero iota).mpr ha) (hupper x i hi α hα)
  simpa only [map_inv₀] using hinverse x i hi α hα

end WeilConjectures.NativeL2
