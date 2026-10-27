module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.IsPrimary
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
import WeilConjectures.AlgebraicGeometry.Regular

/-! # Primary ideals in finite normal power-series algebras

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, V 2.2.3 and V 3.2.3(i),(ii),
printed pp. 65, 67 (blueprint: lem-per-normal-finite-primary-dichotomy).

The field case and the complete discrete valuation ring case are stated separately.
In the latter, the symbolic power is written as the contraction of the extension of
`P ^ n` to `Localization.AtPrime P`, exactly as in the node.
-/

@[expose] public section

universe u v

namespace MvPowerSeries

/-- Over a field, a nonzero proper primary ideal in a finite normal domain over
`Λ[[t₁, ..., tᵣ]]` contains a nonzero element of that power-series ring.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, V 2.2.3(ii), printed p. 65.
(blueprint: lem-per-normal-finite-primary-dichotomy).

Proof: By lem-weil-pbc-finite-algebra-is-integral, the finite algebra is integral.
The zero ideal of `A` is prime, and is strictly contained in `Q` since `Q` is nonzero.
Apply lem-weil-pbc-integral-incomparability in its strict-contraction form to these
ideals; its upper ideal need not be prime. The contraction of zero is zero by
injectivity of the structure map. Thus the contraction of `Q` is nonzero, and any
nonzero element in it is the required `g`. -/
theorem exists_nonzero_mem_primary_of_finite_normal_field
    (Λ : Type u) [Field Λ] (r : ℕ) (hr : 1 ≤ r)
    (A : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra (MvPowerSeries (Fin r) Λ) A] [Module.Finite (MvPowerSeries (Fin r) Λ) A]
    (hinj : Function.Injective (algebraMap (MvPowerSeries (Fin r) Λ) A))
    (Q : Ideal A) (hQ0 : Q ≠ ⊥) (hQ : Q.IsPrimary) :
    ∃ g : MvPowerSeries (Fin r) Λ,
      g ≠ 0 ∧ algebraMap (MvPowerSeries (Fin r) Λ) A g ∈ Q := by
  sorry

/-- Over a complete DVR, a nonzero proper primary ideal in a finite normal domain
above `Λ[[t₁, ..., tᵣ]]` either contains a base series nonzero modulo the uniformizer,
or is a positive symbolic power of its height-one radical, which contains that
uniformizer. Height one is expressed by the absence of an intermediate prime
between zero and the nonzero prime `P`.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, V 3.2.3(i),(ii), printed p. 67.
(blueprint: lem-per-normal-finite-primary-dichotomy).

Proof:
1. By lem-weil-pbc-finite-algebra-is-integral the base inclusion is integral.
   Apply lem-weil-pbc-integral-incomparability to the strict inclusion of zero in
   `Q`. Injectivity identifies the contraction of zero with zero, so `Q` has a
   nonzero contraction to the power-series ring `R`.
2. Coefficientwise reduction `R → (Λ/(π))[[t₁, ..., tᵣ]]` has kernel `πR`:
   choose a quotient by `π` for every coefficient in its kernel. The target is a
   domain by lem-weil-pbc-power-series-domain. Thus `πR` is prime, and is nonzero
   since `π` has nonzero constant coefficient. The DVR is Noetherian, and so is
   `R` by lem-weil-pbc-power-series-noetherian. Applying
   lem-sfb-krull-principal-ideal-height-bound to `πR` makes it height one.
3. If the contraction of `Q` is not contained in `πR`, any element in the difference
   gives the first alternative by step 2. Otherwise put `P = √Q`. Primaryness
   makes this a proper prime: if `(ab)^h ∈ Q` and no power of `a` belongs to `Q`,
   primaryness forces a power of `b` into `Q`. The radical is an ideal by the
   binomial expansion. Its contraction is a nonzero prime contained in `πR`:
   powers in the contraction of `Q` belong to `πR`, which is radical. The
   height-one assertion of step 2 forces this contraction to equal `πR`, so `π ∈ P`.
4. A prime between `πA` and `P` contracts to `πR`; integral incomparability makes
   it equal to `P`. Hence `P` is minimal over `πA` and has height at most one by
   lem-sfb-krull-principal-ideal-height-bound. Its nonzero element `π` makes its
   height exactly one, since both structure maps are injective.
5. Put `B = A_P`. It is local, Noetherian by lem-weil-pbc-localization-noetherian,
   and a normal domain by lem-weil-pbc-localization-normal-domain. By
   lem-weil-pbc-localization-dimension-chains-below-prime its dimension is one:
   the chain `0 < P` exists and there is no longer chain below `P`. Thus
   lem-sc-normal-dim1-dvr makes `B` a DVR. Moreover `Q` is the contraction of
   `QB`: if `a/1 ∈ QB`, clearing denominators gives `sa ∈ Q` with `s ∉ P`.
   If `a ∉ Q`, primaryness gives a power of `s` in `Q`, a contradiction. The
   reverse inclusion is immediate. Consequently `QB` is proper, and domain
   localization and `Q ≠ 0` make it nonzero.
6. Write `QB = bB` with `b ≠ 0`. The DVR factorization
   lem-weil-pbc-dvr-unit-times-uniformizer-power gives `b = uϖ^n`, where `ϖ`
   generates the maximal ideal of `B`. Properness forces `n ≥ 1`. Hence
   `QB = (PB)^n = P^n B`; extension commutes with powers by distributing finite
   sums. Contracting back using step 5 yields exactly `Q = P^(n)`. -/
theorem primary_dichotomy_of_finite_normal_complete_dvr
    (Λ : Type u) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
    [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (r : ℕ) (hr : 1 ≤ r)
    (A : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra (MvPowerSeries (Fin r) Λ) A] [Module.Finite (MvPowerSeries (Fin r) Λ) A]
    (hinj : Function.Injective (algebraMap (MvPowerSeries (Fin r) Λ) A))
    (Q : Ideal A) (hQ0 : Q ≠ ⊥) (hQ : Q.IsPrimary)
    (π : Λ) (hπ : IsLocalRing.maximalIdeal Λ = Ideal.span {π}) :
    (∃ g : MvPowerSeries (Fin r) Λ,
      algebraMap (MvPowerSeries (Fin r) Λ) A g ∈ Q ∧
      MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span {π})) g ≠ 0) ∨
    ∃ P : PrimeSpectrum A,
      P.asIdeal = Q.radical ∧ P.asIdeal ≠ ⊥ ∧
      (∀ T : Ideal A, T.IsPrime → ⊥ < T → T < P.asIdeal → False) ∧
      algebraMap (MvPowerSeries (Fin r) Λ) A (MvPowerSeries.C π) ∈ P.asIdeal ∧
      ∃ n : ℕ, 1 ≤ n ∧
        Q = Ideal.comap (algebraMap A (Localization.AtPrime P.asIdeal))
          (Ideal.map (algebraMap A (Localization.AtPrime P.asIdeal)) (P.asIdeal ^ n)) := by
  sorry

end MvPowerSeries
