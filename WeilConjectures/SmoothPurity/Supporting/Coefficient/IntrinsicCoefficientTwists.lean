/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientTwistsDetailed
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison

/-! # Tate twists in the intrinsic common-stage category

## Implementation details

The completed root line and its signed tensor powers are existing constructions; only their
membership in the intrinsic integral category needs a new interface. The common-stage twist is
the existing derived tensor with this coefficient object. The `Qbar` twist is represented over
the least finite coefficient field, since scalar extension to any larger stage is already part
of common-stage derived tensor. In `intrinsicQbarComplexTwistFunctor` the constant factor has
identity maps; all maps and coefficient comparisons are those of the derived-tensor bifunctor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe d u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

variable (D : FiniteFieldDatum.{d}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]

/-- The signed completed root line is intrinsically constructible and complete. -/
theorem intrinsicIntegralCoefficientTwist_mem (m : ℤ) :
    sfIntegralConstructible l E W (integralCoefficientTwist D l hl E W m) := by
  obtain ⟨hc, a, b, hab, hr⟩ :=
    integralCoefficientTwist_constructible D l hl E W m
  refine ⟨(sfDerivedComplete_iff_legacy l E W D hl _).mpr hc, a, b, hab, ?_⟩
  intro n
  exact ⟨(hr n).1, (hr n).2⟩

/-- The completed root line in the intrinsic integral full subcategory. -/
def intrinsicIntegralCoefficientTwist (m : ℤ) : sfIntegralConstructibleCategory l E W :=
  ⟨integralCoefficientTwist D l hl E W m,
    intrinsicIntegralCoefficientTwist_mem D l hl E W m⟩

variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

/-- The coefficient twist represented over the least finite coefficient field. -/
def intrinsicQbarCoefficientTwist (m : ℤ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  ⟨Padic.finiteCoefficientBase l Ω,
    (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) W).obj
      (intrinsicIntegralCoefficientTwist D l hl
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
          (Padic.finiteCoefficientBase l Ω)) W m)⟩

/-- `K(m)` is `K` tensored with the signed coefficient line, on the intrinsic common-stage
category. -/
def intrinsicQbarComplexTwistFunctor (m : ℤ) :
    generalAlgebraicallyClosedConstructibleCategory l Ω W ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω W :=
  (𝟭 (generalAlgebraicallyClosedConstructibleCategory l Ω W)).prod'
      ((Functor.const (generalAlgebraicallyClosedConstructibleCategory l Ω W)).obj
        (intrinsicQbarCoefficientTwist D l hl W Ω m)) ⋙
    commonStageDerivedTensor l Ω W

end WeilConjectures
