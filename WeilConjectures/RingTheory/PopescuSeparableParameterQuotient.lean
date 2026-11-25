/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.FieldTheory.SeparableExtension
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import WeilConjectures.RingTheory.PopescuDelocalizeHeightZero
import WeilConjectures.RingTheory.PopescuResolutionIdentity
import WeilConjectures.RingTheory.PopescuParameterQuotientData
import WeilConjectures.RingTheory.PopescuParameterQuotientLocalResolution
import WeilConjectures.RingTheory.PopescuParameterQuotientPrimeGeometry

/-!
# Resolving the nilpotent parameter quotient

The quotient by positive powers of a full system of parameters can be resolved over the
corresponding quotient of the polynomial base.

## Implementation details

No minimal-singular-prime assumption on the unreduced algebra is needed. The quotient map and
quotient prime are the canonical ones, determined by the displayed compatibility equalities.
The case `d = 0` is included.

## References

* [Stacks, Tag 07FE] (last paragraph of the proof)
-/

@[expose] public section

universe u v w

namespace Algebra

/-- The quotient by positive powers of a full system of parameters can be resolved over
the corresponding quotient of the polynomial base. -/
theorem exists_popescu_resolution_parameter_quotient
    {k : Type u} {C : Type v} {Λ : Type w}
    [Field k] [CommRing C] [CommRing Λ] [Algebra k Λ]
    (d c : ℕ) (hc : 1 ≤ c) (φ : MvPolynomial (Fin d) k →ₐ[k] Λ)
    [Algebra (MvPolynomial (Fin d) k) C]
    [FinitePresentation (MvPolynomial (Fin d) k) C]
    (γ : letI := φ.toRingHom.toAlgebra; C →ₐ[MvPolynomial (Fin d) k] Λ)
    (q : PrimeSpectrum Λ) [IsNoetherianRing Λ]
    [IsRegularLocalRing (Localization.AtPrime q.asIdeal)]
    (hdim : ringKrullDim (Localization.AtPrime q.asIdeal) = (d : WithBot ℕ∞))
    (hgen : Ideal.span (Set.range (fun i : Fin d ↦
      algebraMap Λ (Localization.AtPrime q.asIdeal) (φ (MvPolynomial.X i)))) =
      IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
    (hsep : IsSeparableExtension k q.asIdeal.ResidueField) :
    letI := φ.toRingHom.toAlgebra
    let J : Ideal (MvPolynomial (Fin d) k) :=
      Ideal.span (Set.range (fun i : Fin d ↦ (MvPolynomial.X i ^ c) ^ 8))
    let J_C := Ideal.map (algebraMap (MvPolynomial (Fin d) k) C) J
    let J_Λ := Ideal.map (algebraMap (MvPolynomial (Fin d) k) Λ) J
    ∃ (_ : FinitePresentation (MvPolynomial (Fin d) k ⧸ J) (C ⧸ J_C))
      (γ₀ : (C ⧸ J_C) →ₐ[MvPolynomial (Fin d) k ⧸ J] (Λ ⧸ J_Λ))
      (q₀ : PrimeSpectrum (Λ ⧸ J_Λ)),
      γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
        (Ideal.Quotient.mk J_Λ).comp γ.toRingHom ∧
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
      CanBePopescuResolved γ₀ q₀ := by
  let := φ.toRingHom.toAlgebra
  dsimp
  obtain ⟨hfp, γ₀, q₀, hcompat, hcomap⟩ :=
    parameter_quotient_data d c hc φ γ q hgen
  refine ⟨hfp, γ₀, q₀, hcompat, hcomap, ?_⟩
  obtain ⟨hdim₀, hminimal⟩ :=
    parameter_quotient_prime_geometry d c φ q hgen hfp γ₀ q₀ hcomap
  by_cases hle : popescuIdeal γ₀ ≤ q₀.asIdeal
  · exact canBePopescuResolved_of_local_height_zero γ₀ q₀ (hminimal hle)
      (parameter_quotient_local_resolution d c hc φ γ q hdim hgen hsep
        hfp γ₀ q₀ hcompat hcomap) hdim₀
  · exact canBePopescuResolved_of_ideal_not_le γ₀ q₀ hle

end Algebra
