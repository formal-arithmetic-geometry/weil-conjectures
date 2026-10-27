module

public import Mathlib.RingTheory.Trace.Defs
public import Mathlib.RingTheory.Valuation.ValuationRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Algebra.Order.Ring.IsNonarchimedean

/-! # Prime-to-residue-characteristic normalized finite trace

Source: agent-supplied coefficient-normalization supplement to Temkin, Stable modification
of relative curves, Proposition 6.2.4, proof, printed p. 47; the power estimate uses
Lemma 6.2.10(i), printed p. 46. This supplement is not a theorem stated by Temkin.
(blueprint: lem-trf-prime-to-p-trace-frobenius-bound)

The degree-normalized finite trace is defined directly from the field trace, including
in positive characteristic. Its linear-map type records linearity.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- The finite field trace divided by the extension degree, as an `F`-linear map.
Source: agent-supplied normalized-trace supplement to Temkin, Proposition 6.2.4,
proof, printed p. 47. (blueprint: lem-trf-prime-to-p-trace-frobenius-bound) -/
noncomputable def finiteDegreeNormalizedTrace (F : Type u) (E : Type v)
    [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] : E →ₗ[F] F :=
  (Module.finrank F E : F)⁻¹ • Algebra.trace F E

/-- Prime-to-residue-characteristic finite Galois averaging fixes the base field,
is nonexpanding, and commutes with the `p`th power up to the stated error.
Source: agent-supplied supplement to Temkin, Proposition 6.2.4, proof, printed p. 47,
using Lemma 6.2.10(i), printed p. 46.
(blueprint: lem-trf-prime-to-p-trace-frobenius-bound)

Proof plan:
1. The ultrametric inequality bounds every integer by one. Since `p` does not divide
   the degree `n`, its residue is nonzero, so `‖n‖ = ‖n⁻¹‖ = 1`. Compatibility induces
   an injection on residue fields, hence the residue characteristic of `E` is also `p`.
   The unit-ball quotient is a field: a nonzero residue is represented by an element
   of norm one, whose inverse is again integral. Also `n ≥ 1`.
2. Matrices of multiplication are additive and commute with scalar multiplication.
   Taking their diagonal sums proves trace linearity; a scalar has matrix `c I`,
   so its trace is `n c` and the normalized trace fixes `c`.
3. For each Galois automorphism, compare the given norm with its pullback.
   The algebraic-absolute-value uniqueness lemma
   `lem-sfb-algebraic-absolute-value-unique` gives invariance of the norm.
4. By `lem-trf-galois-trace-sum`, the trace is the sum of all conjugates. Apply
   `lem-trf-nonarchimedean-finite-sums` and step 3 to bound that sum by `‖x‖`.
   Division by `n` preserves the norm bound.
5. Put `S = ∑ σ, σ x` and `U = ∑ σ, σ (x^p)`. The first inequality of
   `lem-trf-nonarchimedean-prime-power-root-estimates`, at exponent `p^1`, gives
   `‖S^p - U‖ ≤ ‖p‖ * ‖x‖^p`. Apply it also to the `n` copies of one to get
   `‖n^p - n‖ ≤ ‖p‖`, hence `‖n^(p-1) - 1‖ ≤ ‖p‖`.
6. Expand the error as `n⁻ᵖ (U-S^p) + n⁻¹ (1-n^(1-p)) U` in `E`.
   Step 4 at `x^p` bounds `‖U‖` by `‖x‖^p`. Steps 1 and 5 bound each summand
   by `‖p‖ * ‖x‖^p`; the ultrametric inequality and norm compatibility finish.
   In characteristic `p`, the right-hand side is zero. -/
theorem finiteDegreeNormalizedTrace_primeTo_residueChar
    (F : Type u) (E : Type v) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [IsUltrametricDist F] [IsUltrametricDist E] [CompleteSpace F] [CompleteSpace E]
    [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
    (hcompat : ∀ c : F, ‖algebraMap F E c‖ = ‖c‖)
    (p : ℕ) (hp : 0 < p)
    [CharP (IsLocalRing.ResidueField (NormedField.valuation (K := F)).integer) p]
    (hn : ¬ p ∣ Module.finrank F E) :
    (∀ c : F, finiteDegreeNormalizedTrace F E (algebraMap F E c) = c) ∧
      ∀ x : E, ‖finiteDegreeNormalizedTrace F E x‖ ≤ ‖x‖ ∧
        ‖finiteDegreeNormalizedTrace F E (x ^ p) - (finiteDegreeNormalizedTrace F E x) ^ p‖ ≤
          ‖(p : F)‖ * ‖x‖ ^ p := by
  sorry

end Algebra
