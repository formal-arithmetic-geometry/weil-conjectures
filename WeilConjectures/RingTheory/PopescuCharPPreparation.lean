/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.PopescuResolution
public import WeilConjectures.RingTheory.StrictlyStandardElement
public import WeilConjectures.RingTheory.EssentiallySmooth
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import WeilConjectures.RingTheory.PopescuCharPPreparationCore
import WeilConjectures.RingTheory.PopescuCharPPreparationQuotient

/-!
# The auxiliary eighth-power problem in positive characteristic

The construction part of the positive characteristic case of the local resolution step in
Popescu's theorem: an auxiliary polynomial base, a standardized algebra, and an essentially smooth
factorization of the local eighth-power quotient problem.

## Implementation details

The algebra `B = A[x_i, z_ij] / (x_i^(2N) - ∑_j z_ij a_j)` is improved to a standard retract `C`.
Tag 07FH gives a polynomial localization with an essentially smooth Artinian factor `D`, Ogoma's
lemma scales the parameters `π_i`, and Tag 07FI enlarges `D` to solve
`(δ_i π_i)^(2N) = ∑_j a_j λ_ij`. With `n = N + d e`, the map from `B` factors through `D'[t]` modulo
the eighth powers of the parameters. When `d = 0` the parameter list is padded by one zero.
Finitely presented and essentially smooth algebras are transported to representatives in
universe `max u v`.

## References

* [Stacks, Tag 07FJ] (items on powers through the eighth resolution)
* [Stacks, Tag 07FH]
* [Stacks, Tag 07FI]
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra

/-- Construct the auxiliary polynomial base and standardized algebra, together with an
essentially smooth factorization of the local eighth-power quotient problem. This is the
construction part of the positive characteristic case; the statement does not assert a
resolution of the original map. -/
theorem exists_popescu_char_p_preparation
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (hminimal : q.asIdeal ∈ (popescuIdeal α).minimalPrimes) :
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (C : Type (max u v)) (_ : CommRing C) (_ : Algebra k C)
      (_ : Algebra (MvPolynomial (Fin m) k) C)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) C)
      (_ : FinitePresentation (MvPolynomial (Fin m) k) C)
      (β : A →ₐ[k] C) (γ : C →ₐ[MvPolynomial (Fin m) k] Λ),
      (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ ∧
      ∃ (r : ℕ) (π : Fin r → MvPolynomial (Fin m) k),
        1 ≤ r ∧
        (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
        (∀ (i : Fin r)
          (x : MvPolynomial (Fin m) k ⧸ Ideal.span
            {y | ∃ j : Fin r, j.val < i.val ∧ y = π j ^ 8}),
          π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
        (∀ (i : Fin r)
          (x : Λ ⧸ Ideal.span
            {y | ∃ j : Fin r, j.val < i.val ∧
              y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
          π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
        (∀ i, IsStrictlyStandardElement
          (R := MvPolynomial (Fin m) k) (algebraMap (MvPolynomial (Fin m) k) C (π i))) ∧
        let R := MvPolynomial (Fin m) k
        let J := Ideal.span (Set.range (fun i : Fin r ↦ π i ^ 8))
        let J_C := J.map (algebraMap R C)
        let J_Λ := J.map (algebraMap R Λ)
        let R₀ := R ⧸ J
        let C₀ := C ⧸ J_C
        let Λ₀ := Λ ⧸ J_Λ
        ∃ (_ : FinitePresentation R₀ C₀) (γ₀ : C₀ →ₐ[R₀] Λ₀)
          (q₀ : PrimeSpectrum Λ₀),
          γ₀.toRingHom.comp (Ideal.Quotient.mk J_C) =
            (Ideal.Quotient.mk J_Λ).comp γ.toRingHom ∧
          PrimeSpectrum.comap (Ideal.Quotient.mk J_Λ) q₀ = q ∧
          (¬ popescuIdeal γ₀ ≤ q₀.asIdeal ∨
            q₀.asIdeal ∈ (popescuIdeal γ₀).minimalPrimes ∧
            ringKrullDim (Localization.AtPrime q₀.asIdeal) = 0 ∧
            let P := Localization.AtPrime (q₀.asIdeal.under R₀)
            let L := Localization.AtPrime q₀.asIdeal
            letI := Localization.AtPrime.algebraOfLiesOver
              (q₀.asIdeal.under R₀) q₀.asIdeal
            ∃ (E : Type (max u v)) (_ : CommRing E) (_ : Algebra P E),
              EssentiallySmooth P E ∧
              ∃ (f : P ⊗[R₀] C₀ →ₐ[P] E) (g : E →ₐ[P] L),
                g.comp f = Algebra.TensorProduct.lift (Algebra.ofId P L)
                  ((IsScalarTower.toAlgHom R₀ Λ₀ L).comp γ₀)
                  (fun _ _ ↦ Commute.all _ _)) := by
  obtain ⟨m, instΛ, towerΛ, C, instC, algC, algRC, towerC, fpC, β, γ,
    hcomp, hideal, r, π, hparam⟩ :=
    exists_popescu_char_p_preparation_core p hp α q hreg hminimal
  let _ := instΛ
  let _ := towerΛ
  let _ := instC
  let _ := algC
  let _ := algRC
  let _ := towerC
  let _ := fpC
  refine ⟨m, inferInstance, inferInstance, C, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, β, γ, hcomp, hideal, r, π, ?_⟩
  obtain ⟨hr, hπq, hR, hΛ, hstandard, hconstruction⟩ := hparam
  refine ⟨hr, hπq, hR, hΛ, hstandard, ?_⟩
  exact popescu_char_p_preparation_quotient p hp α q m C β γ r π
    ⟨hcomp, hideal⟩ ⟨hr, hπq, hR, hΛ, hstandard⟩ hconstruction


end Algebra
