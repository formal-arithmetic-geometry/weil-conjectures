module

public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Lattice-supported formal power series as a module retract

Source: auxiliary subgroup-support convolution argument, steps 1--5 of
`lem-trf-lattice-support-coefficient-retraction`, refining steps 8--9 of
`lem-trf-completed-monoid-support-projection`. Illusie--Laszlo--Orgogozo,
Expose VI 1.6(i)--(ii), printed p. 70, supplies motivating completed monoid models only.
(blueprint: lem-trf-lattice-support-coefficient-retraction)
-/

universe u v

@[expose] public section

namespace MvPowerSeries

/-- Series supported on the nonnegative part of an integer lattice subgroup form a
subalgebra, and coefficient deletion is an additive module retraction. The subalgebra
and projection are specified by their carrier and coefficients, respectively. The last
clause transports the projection through any injective algebra map onto that subalgebra;
its scalar identity is linearity for the action `t • b = φ t * b`.

Source: auxiliary agent algebra in steps 1--5 of this node, refining steps 8--9 of
`lem-trf-completed-monoid-support-projection`; Illusie--Laszlo--Orgogozo,
Expose VI 1.6(i)--(ii), printed p. 70, is motivation only.
(blueprint: lem-trf-lattice-support-coefficient-retraction)

Proof plan: (1) subgroup subtraction gives `u + w ∈ M ↔ w ∈ M` whenever `u ∈ M`.
(2) The supported coefficient families are closed under addition, negation, constants,
and multiplication: in the finite convolution at an exponent outside the subgroup,
each summand has an unsupported factor. (3) Delete the unsupported coefficients;
coefficientwise addition makes this additive, and supported series are fixed.
(4) In the finite convolution for `a * b`, terms whose first exponent is unsupported
vanish. For every remaining term, step (1) identifies membership of the total exponent
with membership of the second exponent. This proves `π (a * b) = a * π b`.
(5) The image hypothesis gives a unique preimage under `φ` of each `π b`. Injectivity
transports additivity, the scalar identity from (4), and the fixed-point identity
from (3) to this map `ρ`; it also proves uniqueness from the defining equation alone.
Only finite coefficient sums are used, with no completeness or finiteness assumptions.
-/
theorem lattice_support_coefficient_retraction
    (L : Type u) [CommRing L] (r : ℕ) (M : AddSubgroup (Fin r → ℤ)) :
    ∃ S : Subalgebra L (MvPowerSeries (Fin r) L),
      (∀ F : MvPowerSeries (Fin r) L,
        F ∈ S ↔ ∀ e : Fin r →₀ ℕ, (fun i ↦ (e i : ℤ)) ∉ M → coeff e F = 0) ∧
      ∃ π : MvPowerSeries (Fin r) L →+ S,
        (∀ (F : MvPowerSeries (Fin r) L) (e : Fin r →₀ ℕ),
          (((fun i ↦ (e i : ℤ)) ∈ M →
              coeff e (π F : MvPowerSeries (Fin r) L) = coeff e F) ∧
            ((fun i ↦ (e i : ℤ)) ∉ M →
              coeff e (π F : MvPowerSeries (Fin r) L) = 0))) ∧
        (∀ a : S, π (a : MvPowerSeries (Fin r) L) = a) ∧
        (∀ (a : S) (b : MvPowerSeries (Fin r) L),
          π ((a : MvPowerSeries (Fin r) L) * b) = a * π b) ∧
        ∀ (R : Type v) [CommRing R] [Algebra L R]
            (φ : R →ₐ[L] MvPowerSeries (Fin r) L),
          Function.Injective φ → Set.range φ = (S : Set (MvPowerSeries (Fin r) L)) →
          ∃ ρ : MvPowerSeries (Fin r) L →+ R,
            (∀ b : MvPowerSeries (Fin r) L, φ (ρ b) = (π b : MvPowerSeries (Fin r) L)) ∧
            (∀ (t : R) (b : MvPowerSeries (Fin r) L), ρ (φ t * b) = t * ρ b) ∧
            (∀ t : R, ρ (φ t) = t) ∧
            ∀ ρ' : MvPowerSeries (Fin r) L →+ R,
              (∀ b : MvPowerSeries (Fin r) L,
                φ (ρ' b) = (π b : MvPowerSeries (Fin r) L)) → ρ' = ρ := by
  sorry

end MvPowerSeries
