/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteConstantCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.CompactSupportStrictScalarMate
public import WeilConjectures.AlgebraicGeometry.CompactSupportScalarLimitReduction
public import WeilConjectures.AlgebraicGeometry.PurityFiniteSetting
public import WeilConjectures.AlgebraicGeometry.FiniteTorAmplitudeSites

import WeilConjectures.AlgebraicGeometry.ScalarRefinementOriginsE
import WeilConjectures.AlgebraicGeometry.CompactSupportCoefficientModels
import all WeilConjectures.AlgebraicGeometry.CompletedIntegralFiniteFree

/-! F-side finite etale-origin witnesses for strict scalar refinements.

This is the F component of the origin conjunction used by the strict scalar
refinement theorem. Its proof is the finite-coefficient constructible-origin
argument applied independently at each reduction level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.StrictTower
namespace WeilConjectures.PurStrictScalar

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (F : Type u) [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
  (i : E →ₐ[ℚ_[l]] F)

variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
  {X Y : Scheme.{u}}
  [Xbase : X.Over (Spec (.of D.k))]
  [Ybase : Y.Over (Spec (.of D.k))]
  [Xft : LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [Xqc : QuasiCompact (X ↘ Spec (.of D.k))]
  [Xs : IsSeparated (X ↘ Spec (.of D.k))]
  [Yft : LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
  [Yqc : QuasiCompact (Y ↘ Spec (.of D.k))]
  [Ys : IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [fbase : f.IsOver (Spec (.of D.k))]
  [fs : IsSeparated f] [fft : LocallyOfFiniteType f] [fqc : QuasiCompact f]
include D hl Xbase Ybase Xft Xqc Xs Yft Yqc Ys fbase fs fft fqc

/-- F-side origins after completed scalar extension, one witness per level.
Source: Stacks 09AK--09AL; auxiliary Step 1 of
`lem-pur-compact-support-strict-scalar-refinement`
(blueprint: lem-pur-compact-support-strict-scalar-refinement-origins-f).
Proof: the integer inclusion sends the source uniformizer to a unit times a positive
power of the target uniformizer. Mapping its principal ideal gives the ramification
hypothesis of compactSupportCoefficientModels_scalar, whose first conclusion makes the
completed scalar extension finite-Tor constructible integral. Apply the existing E-side
origin theorem with coefficient field F to that object. Its finite-coefficient origin
argument and scalar restriction provide the required witnesses independently at each level.
-/
theorem scalar_refinement_origins_F
    (S' : CoefficientDerivedSystemCalculus.{u, u} l F X)
    (M : DerivedCategory (scalarReductionSource l E X))
    (_hM : finiteTorConstructibleIntegral l E X M) :
    ∀ n : ℕ, Nonempty (ScalarEtaleOrigin
      (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) X
      ((ev (ULift.{u + 1} (Padic.coefficientExtensionIntegers l F)) X n).obj
        ((reduction l F X S').obj
          ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M)))) := by
  obtain ⟨a, e, hepos, ha⟩ := integral_ramification l E F i
  have he : PurCompactSupport.Ramification l E F i e := by
    simp only [PurCompactSupport.Ramification, Padic.coefficientExtensionIdeal,
      pow_one, Ideal.map_span, Set.image_singleton]
    rw [ha, Ideal.span_singleton_mul_left_unit a.isUnit, Ideal.span_singleton_pow]
  have hF := (compactSupportCoefficientModels_scalar l E F i D hl e hepos he X M _hM).1
  exact scalar_refinement_origins_E l F D hl f S'
    ((pbcDerivedExtend (completedCoefficientMap l E F i X)).obj M) hF

end WeilConjectures.PurStrictScalar
