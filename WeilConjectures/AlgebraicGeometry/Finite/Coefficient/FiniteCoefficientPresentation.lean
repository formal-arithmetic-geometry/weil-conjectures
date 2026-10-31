/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingData
import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRingOrientationSupport

/-! # The finite prime-coefficient presentation

Source: current general-ring smooth purity, paragraph (1).
(blueprint: lem-sp-finite-prime-coefficient-presentation). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale

/-- Present the bottom finite quotient by the prime ring, and extend its root line.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-thm-smooth-purity/sk-thm-smooth-purity-general-ring.proof.md, paragraph (1).
(blueprint: lem-sp-finite-prime-coefficient-presentation).

Proof: identify the bottom intermediate field with Q_ell by its structural map.
Its valuation ring is Z_ell, since the extended spectral norm restricts to the
p-adic norm. The maximal ideal corresponds to (ell), and the nth power corresponds
to (ell^n). Reduction modulo this ideal gives Z/(ell^n), including its unital
ring structure (`primeQuotientEquiv`).
For the second datum, sheafify the balanced map sending a tensor z to phi(a)
tensor z on the common Kummer root sheaf. Its adjunction transpose extends the
root line. On a finite etale cover splitting the roots, both lines are free on
the same primitive root and this map is the identity on the coefficient B.
Consequently it is an isomorphism for every B killed by ell^n, without flatness.
The line is flat, so the degree-zero derived scalar comparison is the localization
of this ordinary map (`generalRingCoefficientLine`, with the identity root map).
At the zero ring the same maps are the unique maps of zero modules; the argument
also covers empty schemes.
-/
theorem finitePrimeCoefficientPresentation
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (hEll : ell ≠ D.p) (n : ℕ) (hn : 1 ≤ n)
    (A : Type u) [CommRing A] [Finite A] (hA : ((ell ^ n : ℕ) : A) = 0)
    (T : Scheme.{u}) (hT : IsUnit ((ell ^ n : ℕ) : Γ(T, ⊤))) :
    let P := finiteGeneralRingPrimeSetting D ell hEll n hn
    ∃ e : P.Ring ≃+* ULift.{u} (ZMod P.diagonalExponent),
      Nonempty (Etale.FiniteSmoothPurity.CoefficientLineComparison
        (RingHom.ulift.{u + 1, u + 1, u, u} (finiteGeneralRingCoefficientMap P A hA e))
        P.diagonalExponent P.diagonalExponent P.diagonalExponent_annihilates
        (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) T) := by
  intro P
  obtain ⟨e⟩ := primeQuotientEquiv D ell hEll n hn
  exact ⟨e, generalRingCoefficientLine _ P.diagonalExponent
    (pow_pos P.coefficients.prime.out.pos P.level) P.diagonalExponent_annihilates
    (congrArg (fun a : A ↦ (⟨a⟩ : ULift.{u + 1, u} A)) hA) T hT⟩

end AlgebraicGeometry.ProEtale
