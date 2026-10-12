module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.AlgebraicGeometry.IntegralOverringJacobsonPower
import Sheaf.RingTheory.FiniteIntegralConductor

/-! # Conductor powers in a semilocal normalization

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09N2.
(blueprint: semilocal-dim-one-conductor-power)
-/

@[expose] public section
universe u v

/-- Conductor-power conclusion for the normalization in Varieties Lemma 09N2.

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09N2.
(blueprint: semilocal-dim-one-conductor-power)

Proof: identify `B` with its image in `K` using the injective fraction-ring map,
put `B' = integralClosure B K`, and let `A = B[x,y]` inside `K`. Both generators
are integral, so `A` is finite over `B`. Since `B ⊆ A ⊆ K` and `K` is the fraction
field of `B`, it is also the fraction field of `A`. The finite conductor theorem
therefore supplies `r > 0` with `J(B)^r A ⊆ B`: every product of a member of
`J(B)^r` with a member of `A` lies in `B`, and so do finite sums of such products.
The inclusions `B ⊆ A ⊆ B'` are injective and integral. Integral lying-over gives
surjectivity of `Spec(B') → Spec(A)`. Apply `integral_overring_jacobson_power`
using the assumed finiteness of the maximal spectra of `B` and `B'`. Since
`x ∈ A` maps into `J(B')`, it yields `m > 0` with `x^m ∈ J(B) A`. Raising to
power `r` puts `x^(m*r)` in `(J(B) A)^r = J(B)^r A`. Multiplying by `y ∈ A`
keeps it in that ideal, hence in `B`. Take `n = m*r > 0` and the corresponding
preimage `b : B` to obtain the equality in `K`. This also works for `y = 0`;
the nonzero hypothesis on `x` is inherited from the source and is not needed
for this part of its argument.
-/
theorem semilocal_dim_one_conductor_power
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    (K : Type v) [Field K] [Algebra B K] [IsFractionRing B K]
    [Finite (MaximalSpectrum (integralClosure B K))] :
    ∀ x y : integralClosure B K,
      x ≠ 0 → x ∈ Ideal.jacobson (⊥ : Ideal (integralClosure B K)) →
        ∃ n : ℕ, 0 < n ∧ ∃ b : B,
          algebraMap B K b = (x : K) ^ n * (y : K) := by
  sorry
