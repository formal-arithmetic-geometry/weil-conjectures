/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Integers in a finite extension of p-adic fields
-/

@[expose] public section

universe u v

namespace Padic

/-- For finite p-adic extensions `E ⊆ F`, the unit ball in `F` is the
integral closure of the unit ball in `E`.
-/
theorem padic_integers_integralClosure
    (l : ℕ) [Fact l.Prime]
    (E : Type u) (F : Type v) [Field E] [Field F]
    [Algebra ℚ_[l] E] [Algebra ℚ_[l] F]
    [FiniteDimensional ℚ_[l] E] [FiniteDimensional ℚ_[l] F]
    (i : E →ₐ[ℚ_[l]] F) (x : F) :
    x ∈ coefficientExtensionIntegers l F ↔
      x ∈ @integralClosure (coefficientExtensionIntegers l E) F _ _
        ((i.toRingHom.comp (coefficientExtensionIntegers l E).subtype).toAlgebra) := by
  classical
  -- The spectral value controls the coefficients of the minimal polynomial directly.
  let O := coefficientExtensionIntegers l E
  let T := coefficientExtensionIntegers l F
  let : Algebra O F := (i.toRingHom.comp O.subtype).toAlgebra
  have hE := (coefficientExtensionIntegers_dvr l E).choose_spec
  have hF := (coefficientExtensionIntegers_dvr l F).choose_spec
  have hmemE (a : E) : a ∈ O ↔ spectralNorm ℚ_[l] E a ≤ 1 := hE.1 a
  have hmemF (a : F) : a ∈ T ↔ spectralNorm ℚ_[l] F a ≤ 1 := hF.1 a
  have hmap (a : E) : spectralNorm ℚ_[l] F (i a) = spectralNorm ℚ_[l] E a := by
    unfold spectralNorm
    rw [minpoly.algHom_eq i i.injective]
  constructor
  · intro hx
    have hmon := minpoly.monic (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) x)
    have hcoeff := (spectralValue_le_one_iff hmon).mp ((hmemF x).mp hx)
    let p := (minpoly ℚ_[l] x).map (algebraMap ℚ_[l] E)
    have hp : p.Monic := hmon.map _
    have hlift : p ∈ Polynomial.lifts O.subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      refine ⟨⟨p.coeff n, (hmemE _).mpr ?_⟩, rfl⟩
      simpa only [p, Polynomial.coeff_map, spectralNorm_extends] using hcoeff n
    obtain ⟨q, hq, _, hqmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hp
    change IsIntegral O x
    refine ⟨q, hqmon, ?_⟩
    change q.eval₂ (i.toRingHom.comp O.subtype) x = 0
    rw [← Polynomial.eval₂_map, hq]
    simp only [p, Polynomial.eval₂_map]
    have hi : i.toRingHom.comp (algebraMap ℚ_[l] E) = algebraMap ℚ_[l] F := by
      ext a
      exact i.commutes a
    rw [hi]
    exact minpoly.aeval ℚ_[l] x
  · intro hx
    -- The larger integer ring is integrally closed in its fraction field.
    have : IsFractionRing T F := hF.2.2.2.2.2.2.1
    have : IsPrincipalIdealRing T := hF.2.2.2.2.2.2.2.2.1
    have : IsIntegrallyClosed T := inferInstance
    have : IsIntegrallyClosedIn T F :=
      (isIntegrallyClosed_iff_isIntegrallyClosedIn F).mp inferInstance
    apply (Subring.integralClosure_le_iff (R := O) (T := T)).mpr ?_ hx
    intro a
    apply (hmemF _).mpr
    change spectralNorm ℚ_[l] F (i (a : E)) ≤ 1
    rw [hmap]
    exact (hmemE _).mp a.property

end Padic
