module
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.RingTheory.FiniteIntegralConductor

/-! The ideal-power form of the finite conductor statement.

Source: literature/stacks-project/varieties.tex, Varieties Lemma 09N2.
(blueprint: semilocal-dim-one-conductor-power-mul)
-/
@[expose] public section
universe u v

/-- If a finite intermediate subalgebra has conductor exponent `r`, every element of
`(J(B)A)^r` multiplied by an element of `A` comes from `B`. The proof expands an element
of the ideal power as a finite sum of products of `r` mapped Jacobson elements, applies
`exists_jacobson_pow_mul_mem_base` to each product, and sums the resulting base elements.

(blueprint: semilocal-dim-one-conductor-power-mul)

Proof: expand membership in the ideal power as a finite sum of products of mapped
Jacobson elements, apply the finite conductor theorem to each product, and sum the
resulting base elements.
-/
theorem Subalgebra.exists_base_mul_mem_of_mem_map_jacobson_pow
    {B : Type u} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hdim : ringKrullDim B = 1)
    {K : Type v} [Field K] [Algebra B K] [IsFractionRing B K]
    (A : Subalgebra B K) [Module.Finite B A] [IsFractionRing A K]
    {r : ℕ} (z : A)
    (hz : z ∈ (Ideal.map (algebraMap B A) (Ideal.jacobson (⊥ : Ideal B))) ^ r)
    (a : A) : ∃ c : B, algebraMap B K c = (z : K) * (a : K) := by
  sorry
