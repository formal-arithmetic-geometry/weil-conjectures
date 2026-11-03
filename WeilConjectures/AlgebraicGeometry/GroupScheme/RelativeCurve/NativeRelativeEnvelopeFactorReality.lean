/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.RelativeCurvePunctual
public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeCondensedWeil.NativeCondensedWeilReality
import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.NativeRelativeCurveSpectrum
import WeilConjectures.AlgebraicGeometry.GroupScheme.RelativeCurve.NativeRelativeCurveAlternatingTrace
import WeilConjectures.DeligneLaumon.Reduction.TraceReality
import WeilConjectures.AlgebraicGeometry.Closed.ClosedPointField

/-! # Reality of the native relative affine-curve factors

Source: latest blueprint, lem-zl-relative-envelope-factor-reality.
(blueprint: lem-zl-relative-envelope-factor-reality)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.RelativeCurve

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  {U₀ Y₀ : Over (Spec (.of D.k₀))}
  [LocallyOfFiniteType U₀.hom] [QuasiCompact U₀.hom]
  [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [hYsep : IsSeparated Y₀.hom]
  (h₀ : U₀ ⟶ Y₀) [hSmooth : SmoothOfRelativeDimension 1 h₀.left]
  [hSep : IsSeparated h₀.left] [hQC : QuasiCompact h₀.left]
  (hAffine : ∀ y : Y₀.left, IsAffine (h₀.left.fiber y))
  (c₀ : Compactification h₀.left) (E : NativeL2.WeilModule D l U₀)
  (hLisse : IsLisseCoefficientModule (Profinite.padicAlgClRingObj l) E.carrier)
  (iota : PadicAlgCl l →+* ℂ)

include hl hYsep hSmooth hSep hQC hAffine hLisse

/-- Real lisse pure-zero coefficients give real native higher compact-support modules.
Source: latest blueprint, lem-zl-relative-envelope-factor-reality and its proof.
(blueprint: lem-zl-relative-envelope-factor-reality)

Proof: at each closed point, degree one has reciprocal-root modulus at most q^(1/2)
by the native punctual bound and degree two has modulus q by top-factor purity.
The trace formula makes every alternating power trace real. Since q>1 these radii
are disjoint, so the reduced-factor reality theorem gives real reverse characteristic
polynomials in degrees one and two. All other groups are zero. The basis-independent
characteristic polynomial equals the matrix polynomial in every chosen finite basis,
which is precisely NativeCondensedWeil.Real.
-/
theorem real_higherShriek_of_isAffine_fiber
    (hReal : NativeCondensedWeil.Real D l U₀ E iota)
    (hPure : NativeL2.Pure D l U₀ E iota 0) (i : ℕ) :
    NativeCondensedWeil.Real D l Y₀ (higherShriek D l h₀ c₀ E i) iota := by
  classical
  intro y ι hι n basis j
  obtain ⟨hfin, hzero, htop⟩ := native_relative_curve_spectrum D l hl h₀ hAffine c₀ E
    hLisse iota hPure y ι hι
  let := hfin 1
  let := hfin 2
  let := hfin i
  let Ω := ULift.{u + 1} (PadicAlgCl l)
  let σ : Ω →+* ℂ := iota.comp ULift.ringEquiv.toRingHom
  let : IsAlgClosed Ω := by
    constructor
    intro p
    have hs := (IsAlgClosed.splits (p.map ULift.ringEquiv.toRingHom)).map
      ULift.ringEquiv.symm.toRingHom
    have he : ULift.ringEquiv.symm.toRingHom.comp
        (ULift.ringEquiv.toRingHom : Ω →+* PadicAlgCl l) = RingHom.id Ω := by
      ext x
      rfl
    rw [Polynomial.map_map, he, Polynomial.map_id] at hs
    exact hs
  let A₁ := (NativeL2.closedOperator D l Y₀ (higherShriek D l h₀ c₀ E 1) y ι hι).hom
  let A₂ := (NativeL2.closedOperator D l Y₀ (higherShriek D l h₀ c₀ E 2) y ι hι).hom
  let := (Y₀.hom.residueFieldAlgebraMap y.val).toAlgebra
  have := (closedPoint_iff_residueField_trdeg_zero_and_finite Y₀.hom y.val).2.1.mp y.prop
  have : Finite (Y₀.left.residueField y.val) := Module.finite_of_finite D.k₀
  have hq : (1 : ℝ) < Nat.card (Y₀.left.residueField y.val) := by
    exact_mod_cast Finite.one_lt_card
  have hgap : (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (1 / 2 : ℝ) <
      (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (1 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hq (by norm_num)
  have h₁ : ∀ α, Module.End.HasEigenvalue A₁ α →
      ‖σ α‖ ≤ (Nat.card (Y₀.left.residueField y.val) : ℝ) ^ (1 / 2 : ℝ) := by
    intro α hα
    change ‖iota α.down‖ ≤ _
    simpa only [zero_add, Nat.cast_one] using
      punctual_bound D l hl h₀ hAffine c₀ E hLisse iota 0 hPure 1 y ι hι α hα
  have htr : ∀ m, m ≠ 0 →
      (starRingEnd ℂ) (σ (LinearMap.trace Ω _ (A₂ ^ m) -
        LinearMap.trace Ω _ (A₁ ^ m))) =
      σ (LinearMap.trace Ω _ (A₂ ^ m) - LinearMap.trace Ω _ (A₁ ^ m)) := by
    intro m hm
    exact native_relative_curve_alternating_trace D l hl h₀ hAffine c₀ E hLisse
      iota hReal y ι hι m hm
  obtain ⟨hr₁, hr₂⟩ := LinearMap.map_charpolyRev_conj_eq_self_of_trace σ A₁ A₂ h₁
    htop hgap htr
  have hfactor : ((NativeL2.closedOperator D l Y₀
      (higherShriek D l h₀ c₀ E i) y ι hι).hom.charpolyRev.map σ).map (starRingEnd ℂ) =
      (NativeL2.closedOperator D l Y₀
        (higherShriek D l h₀ c₀ E i) y ι hι).hom.charpolyRev.map σ := by
    by_cases hi₁ : i = 1
    · subst i
      exact hr₁
    by_cases hi₂ : i = 2
    · subst i
      exact hr₂
    let := hzero i hi₁ hi₂
    simp only [LinearMap.charpolyRev_of_subsingleton, Polynomial.map_one]
  apply Complex.conj_eq_iff_im.mp
  have hcoeff := congrArg (fun p : Polynomial ℂ ↦ p.coeff j) hfactor
  simp only [Polynomial.coeff_map] at hcoeff
  have hb : NativeCondensedWeil.localFactorInBasis D l Y₀
      (higherShriek D l h₀ c₀ E i) y ι hι n basis =
      (NativeL2.closedOperator D l Y₀ (higherShriek D l h₀ c₀ E i) y ι hι).hom.charpolyRev := by
    unfold NativeCondensedWeil.localFactorInBasis NativeL2.closedOperator
    exact (LinearMap.charpoly_toMatrix _ basis).symm ▸ rfl
  rw [hb]
  exact hcoeff

end WeilConjectures.RelativeCurve
