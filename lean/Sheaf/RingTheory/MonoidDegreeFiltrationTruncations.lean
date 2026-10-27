/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-!
# Degree bounds and compatible truncations of a monoid algebra

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI, §1.6(i)–(ii),
printed p. 70, motivates the completed monoid models. The filtration and truncation
argument is auxiliary agent algebra, not an assertion of ILO
(blueprint: lem-trf-monoid-degree-filtration-truncations).
-/

@[expose] public section

universe u

namespace AddMonoidAlgebra

open Classical in
/-- The coefficient-plus-monomial filtration is cofinal with the induced power-series
filtration, and supported series have compatible finite degree truncations.

Source: ILO, Exposé VI, §1.6(i)–(ii), printed p. 70, for the motivating completed
monoid models only; auxiliary agent algebra, steps 1–6 of
lem-trf-monoid-degree-filtration-truncations.
(blueprint: lem-trf-monoid-degree-filtration-truncations).

Exponent vectors use `Fin r →₀ ℕ`, canonically the same as `ℕ^r`. The chosen list
`q` generates the subtype monoid `Q`; its closure is therefore the top submonoid.
The existential witnesses are specified by exact defining equations: `j` is the
finite monomial sum, `J` and `I` are the displayed ideals, `D` is the generator
bound, and `b n` is the finite sum over exponents of degree less than `D * n`.
Thus no arbitrary embedding or unspecified truncation is assumed.

Proof plan:
1. The coefficient at an exponent in `Q` of the finite monomial sum is its original
   coefficient, and it is zero outside `Q`. This proves injectivity. The finite
   convolution formula proves multiplicativity and preservation of constants.
   Nonzero monomials lie in the variables ideal, so `j(J) ⊆ I`, giving `J^n ⊆ E_n`.
2. Write each `q` as a sum of `ell` chosen generators. Then its degree is at most
   `D * ell`, its monomial lies in `J^ell`, and a coefficient in `a^t` gives a term
   in `J^(t + ell)`. For the zero exponent use the empty sum.
3. For a term in `E_(Dn)`, if `ell ≥ n` its monomial is already in `J^n`.
   Otherwise the combined-ideal coefficient criterion
   `lem-weil-pbc-power-series-combined-ideal-coefficients` puts its coefficient in
   `a^(Dn-degree q)`, and `Dn-degree q ≥ n-ell`. Each term is in `J^n`, so is the sum.
4. The exponents of degree less than `Dn` form a finite set, even for `r=0` or `n=0`.
   For `m ≥ n`, each monomial of the truncation difference has degree at least `Dn`;
   the bound `degree q ≤ D * ell` and `D ≥ 1` imply `ell ≥ n`. Hence it lies in `J^n`.
5. The series minus its truncation has zero coefficients below `Dn`, including
   outside `Q` by the support hypothesis. The same combined-ideal criterion puts
   the tail in `I^(Dn)`. The truncation formula also gives exact low coefficients.
6. Step 4 makes the classes compatible under every quotient transition, so they
   define an element of `AdicCompletion J B` with the stated evaluations.
   At level zero the quotient is zero, which includes `n=0`.
-/
theorem monoid_degree_filtration_truncations
    (L : Type u) [CommRing L] (r : ℕ) (Q : AddSubmonoid (Fin r →₀ ℕ))
    (a : Ideal L) (s : ℕ) (q : Fin s → Q)
    (h_nonzero : ∀ i : Fin s, q i ≠ 0)
    (h_generates : AddSubmonoid.closure (Set.range q) = ⊤) :
    ∃ j : AddMonoidAlgebra L Q →ₐ[L] MvPowerSeries (Fin r) L,
      (∀ f : AddMonoidAlgebra L Q,
        j f = f.coeff.sum (fun e c ↦ MvPowerSeries.monomial (e : Fin r →₀ ℕ) c)) ∧
      Function.Injective j ∧
      ∃ (J : Ideal (AddMonoidAlgebra L Q)) (I : Ideal (MvPowerSeries (Fin r) L))
        (D : ℕ),
        J = Ideal.map (algebraMap L (AddMonoidAlgebra L Q)) a ⊔
          Ideal.span {x | ∃ e : Q, e ≠ 0 ∧ x = AddMonoidAlgebra.single e (1 : L)} ∧
        I = Ideal.map (algebraMap L (MvPowerSeries (Fin r) L)) a ⊔
          Ideal.span (Set.range (MvPowerSeries.X : Fin r → MvPowerSeries (Fin r) L)) ∧
        D = max 1 ((Finset.univ : Finset (Fin s)).sup
          (fun i ↦ (q i : Fin r →₀ ℕ).degree)) ∧
        (∀ n : ℕ,
          J ^ n ≤ Ideal.comap j.toRingHom (I ^ n) ∧
          Ideal.comap j.toRingHom (I ^ (D * n)) ≤ J ^ n) ∧
        ∀ F : MvPowerSeries (Fin r) L,
          (∀ e : Fin r →₀ ℕ, e ∉ Q → MvPowerSeries.coeff e F = 0) →
          ∃ b : ℕ → AddMonoidAlgebra L Q,
            (∀ n : ℕ, b n =
              ∑ e ∈ (Finsupp.finite_of_degree_lt (σ := Fin r) (D * n)).toFinset,
                if h : e ∈ Q then
                  AddMonoidAlgebra.single ⟨e, h⟩ (MvPowerSeries.coeff e F) else 0) ∧
            (∀ m n : ℕ, n ≤ m →
              b m - b n ∈ J ^ n ∧ F - j (b n) ∈ I ^ (D * n)) ∧
            (∃ x : AdicCompletion J (AddMonoidAlgebra L Q),
              ∀ n : ℕ, AdicCompletion.evalₐ J n x = Ideal.Quotient.mk (J ^ n) (b n)) ∧
            ∀ (e : Fin r →₀ ℕ) (n : ℕ), e.degree < D * n →
              MvPowerSeries.coeff e (j (b n)) = MvPowerSeries.coeff e F := by
  sorry

end AddMonoidAlgebra
