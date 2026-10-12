/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.RingTheory.PopescuResolution
public import Sheaf.FieldTheory.SeparableExtension
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

import Sheaf.Algebra.PopescuLiftNilpotent
import Sheaf.FieldTheory.SeparableSmoothColimit
import Sheaf.RingTheory.FlatOverRegular
import Sheaf.RingTheory.PolynomialOriginRegularLocal
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.SingularIdeal

@[expose] public section

universe u v w

namespace Algebra

/-- The quotient map has a Popescu resolution after localization at the quotient prime.

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FE, steps 9--12
(blueprint: lem-weil-pbc-popescu-parameter-quotient-local-resolution).

Proof: Put R=k[x_i], e=8c and p=φ⁻¹(q). The parameter hypothesis implies p is the
origin maximal ideal. The d parameters are a regular sequence in the regular local ring
Λ_q of dimension d. The polynomial-origin regular-local theorem and flat-over-regular
criterion give flatness of R_p→Λ_q. Base change gives flatness after quotienting by the
powered parameters. The reduced base has nilpotent maximal ideal: a monomial of total
degree d(e-1)+1 is divisible by some x_i^e. Its residue field is k, and the closed fiber
of the reduced target is κ(q). Separability expresses that fiber as a filtered colimit
of smooth k-algebras; nilpotent lifting expresses the reduced local target as a filtered
colimit of smooth algebras over the reduced local base. Factor the finitely presented
localized source through a smooth stage. A finitely presented stage can be represented
in the universe of the source and base. Its singular ideal is the unit ideal, so the
factorization satisfies the domination and escape conditions of a Popescu resolution.
Canonical quotient/localization isomorphisms identify these maps with the displayed
ones, since their composites with the quotient maps agree. For d=0 the ideals vanish,
the localized base and target are fields, and the same separable smooth-colimit
factorization proves the assertion. No delocalization is asserted here. -/
theorem parameter_quotient_local_resolution
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
    ∀ (_ : FinitePresentation (MvPolynomial (Fin d) k ⧸ J) (C ⧸ J_C))
      (γ₀ : (C ⧸ J_C) →ₐ[MvPolynomial (Fin d) k ⧸ J] (Λ ⧸ J_Λ))
      (q₀ : PrimeSpectrum (Λ ⧸ J_Λ)),
      γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
          (Ideal.Quotient.mk J_Λ).comp γ.toRingHom →
      PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q →
    letI := Localization.AtPrime.algebraOfLiesOver
      (q₀.asIdeal.under (MvPolynomial (Fin d) k ⧸ J)) q₀.asIdeal
    CanBePopescuResolved
      (Algebra.TensorProduct.lift
        (Algebra.ofId (Localization.AtPrime (q₀.asIdeal.under (MvPolynomial (Fin d) k ⧸ J)))
          (Localization.AtPrime q₀.asIdeal))
        ((IsScalarTower.toAlgHom (MvPolynomial (Fin d) k ⧸ J) (Λ ⧸ J_Λ)
          (Localization.AtPrime q₀.asIdeal)).comp γ₀)
        (fun _ _ => Commute.all _ _))
      ⟨IsLocalRing.maximalIdeal (Localization.AtPrime q₀.asIdeal), inferInstance⟩ := by
  sorry

end Algebra
