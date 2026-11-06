/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceLinearTraceInvariance
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.Algebra.CharP.Algebra

/-! # The positive finite coefficient twist in fixed-ring coordinates

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sp-tate-twist,
def-coefficient-twists-detailed, finite reduction and tensor-power clauses
(blueprint: def-coefficient-twists-detailed).

The recorded intrinsic interface reexports signed finite twists as modules over a
coefficient ring sheaf. This module exposes their positive shifted presentation in
fixed-ring module sheaves, as required by the recorded finite exceptional functor.
The first line is the published root line mu_(l^n) tensor A; its d-th tensor power
with shift 2d is the published ordered affineLinearBaseCoefficient. No generator,
orientation or root of unity is chosen. The exponent l^n kills O_E/(varpi^n) at
every positive level, including levels not divisible by the ramification index.
The intrinsic signed, integral, rational and Qbar definitions are provided by
`WeilConjectures.SmoothPurity.Supporting.Coefficient.IntrinsicCoefficientTwists`.

## Main declarations

- `diagonalExponent`: a valid annihilator at every positive finite level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Reuse finiteness of the actual positive coefficient quotient and its size lift.
Source: blueprint fixed finite coefficient level
(blueprint: def-coefficient-twists-detailed). -/
instance diagonalCoefficientFinite (P : PurityFiniteSetting.{u}) : Finite P.Coefficient :=
  letI : Finite P.Ring := Padic.finite_coefficientExtensionRing
    P.coefficients.l P.extension P.level P.level_pos
  inferInstanceAs (Finite (ULift.{u + 1} P.Ring))

/-- Use the positive level itself as an annihilating l-power, without requiring the
ramification index to divide that level. Source: blueprint def-pur-conventions,
finite coefficients (blueprint: def-coefficient-twists-detailed). -/
def diagonalExponent (P : PurityFiniteSetting.{u}) : ℕ := P.coefficients.l ^ P.level

/-- The same exponent is invertible on every k-scheme.
Source: blueprint finite coefficient conventions
(blueprint: def-coefficient-twists-detailed).
Proof: l differs from characteristic p, so its image in k is nonzero and is a unit.
Take its n-th power and apply the structure-map homomorphism on global sections.
This includes the empty scheme. -/
theorem diagonalExponent_isUnit (P : PurityFiniteSetting.{u}) {T : Scheme.{u}}
    (a : T ⟶ Spec (.of P.field.k)) : IsUnit (P.diagonalExponent : Γ(T, ⊤)) := by
  let : Fintype P.field.k₀ := Fintype.ofFinite _
  have : Fact P.field.p.Prime := ⟨P.field.prime⟩
  have : CharP P.field.k₀ P.field.p := charP_of_card_eq_prime_pow (by
    rw [← Nat.card_eq_fintype_card, P.field.card_base, P.field.cardinality_eq])
  have : CharP P.field.k P.field.p :=
    charP_of_injective_algebraMap' P.field.k₀ P.field.p
  have hl : IsUnit (P.coefficients.l : P.field.k) :=
    isUnit_iff_ne_zero.mpr (CharP.cast_ne_zero_of_ne_of_prime _
      (Fact.out : P.coefficients.l.Prime) P.coefficients.different.symm)
  let f := (Scheme.ΓSpecIso (CommRingCat.of P.field.k)).inv ≫ a.appTop
  simpa only [diagonalExponent, map_natCast, Nat.cast_pow] using
    (hl.map f.hom).pow P.level

end WeilConjectures.PurityFiniteSetting
