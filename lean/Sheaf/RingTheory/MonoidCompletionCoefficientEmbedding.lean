module

public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients

/-!
# Coefficient-limit embedding of a completed monoid algebra

Source: Illusie–Laszlo–Orgogozo, Travaux de Gabber, Exposé VI, §1.6(i)–(ii),
printed p. 70, motivates the completed monoid models; the coefficient-limit
argument is the auxiliary algebra of the DAG node
(blueprint: lem-trf-monoid-completion-coefficient-embedding).
-/

@[expose] public section

universe u

namespace AddMonoidAlgebra

/-- The completion of a cofinally filtered monoid subalgebra embeds in power series
by taking limits of its coefficients.

Source: ILO, Exposé VI, §1.6(i)–(ii), printed p. 70 (completed monoid models),
and the auxiliary coefficient-limit argument recorded in the DAG
(blueprint: lem-trf-monoid-completion-coefficient-embedding).

The equations `hJ`, `hI`, and `hj` specify the two ideals and the monomial map;
they introduce no additional choices of algebraic data. Exponents in `ℕ^r` are
encoded by `Fin r →₀ ℕ`, canonically all exponent vectors since `Fin r` is finite.
The topology on the completion is the infimum of the topologies induced by its
projections to discrete quotients. Its zero-neighborhood basis is precisely the
coordinate kernels, without identifying those kernels with extended ideal powers.
The target has `I.adicTopology`, whose zero-neighborhood basis is `I ^ n`.

Proof:
1. Bijectivity of the coefficient completion map implies that the intersection of
   all powers of `a` is zero. Apply
   `lem-weil-pbc-power-series-combined-ideal-coefficients`: membership in `I ^ n`
   means that coefficients of degree below `n` lie in `a ^ (n - degree)`.
   Taking `n = k + degree` proves that the intersection of the powers of `I` is zero.
2. The specified monomial map preserves addition, multiplication and scalars.
   The hypothesis on `J` implies `j (J ^ n) ⊆ I ^ n`. Compatibility of a completion
   element's coordinates makes any two representatives at levels at least
   `k + degree e` have the same coefficient at `e` modulo `a ^ k`.
   Changing a representative does not change that residue either.
3. These residues form a compatible family in the coefficient completion.
   Bijectivity supplies exactly one coefficient in `L`. Assemble the resulting
   family into a power series. This gives the characterization for every choice
   of representatives, and coefficients outside `Q` vanish by separatedness.
4. Componentwise operations in `AdicCompletion` and the finite coefficient
   convolution formula show, modulo every `a ^ k`, that this construction is
   additive and multiplicative. Separatedness makes these equalities in `L`.
   Constant representatives show it extends `j` and preserves all scalars.
5. At index `n`, the coefficient characterization and the combined-ideal criterion
   give `ι x - j (f n) ∈ I ^ n`; for `n = 0` this is automatic. If the nth coordinate
   is zero, `f n ∈ J ^ n`, so also `ι x ∈ I ^ n`.
6. If `ι x = 0`, choose `N ≥ n` by cofinality. The approximation at level `N`
   puts `j (f N)` in `I ^ N`, hence `f N ∈ J ^ n`. Coordinate compatibility makes
   the nth coordinate zero. Every coordinate is zero, proving injectivity.
7. The kernel-image inclusions prove continuity. For fixed `m`, all representatives
   at levels `n ≥ m` have canonical images with the same mth coordinate as `x`.
   Thus their images converge to `x` in the specified inverse-limit topology.
8. Any other continuous algebra map extending `j` takes these approximants to
   `j (f n)`. Continuity and the approximation from step 5 put its difference from
   `ι x` in every power of `I`. Step 1 makes the difference zero, proving uniqueness.
-/
theorem monoidCompletion_coefficientEmbedding
    (r : ℕ) (Q : AddSubmonoid (Fin r →₀ ℕ))
    (L : Type u) [CommRing L] (a : Ideal L)
    (J : Ideal (AddMonoidAlgebra L Q))
    (hJ : J = Ideal.map (algebraMap L (AddMonoidAlgebra L Q)) a ⊔
      Ideal.span {b | ∃ q : Q, q ≠ 0 ∧ b = single q (1 : L)})
    (I : Ideal (MvPowerSeries (Fin r) L))
    (hI : I = Ideal.map (algebraMap L (MvPowerSeries (Fin r) L)) a ⊔
      Ideal.span (Set.range (MvPowerSeries.X : Fin r → MvPowerSeries (Fin r) L)))
    (j : AddMonoidAlgebra L Q →ₐ[L] MvPowerSeries (Fin r) L)
    (hj : ∀ (q : Q) (c : L), j (single q c) = MvPowerSeries.monomial q.1 c)
    (hcomplete : Function.Bijective (AdicCompletion.of a L))
    (hmap : J ≤ Ideal.comap j.toRingHom I)
    (hcofinal : ∀ n : ℕ, ∃ N : ℕ, n ≤ N ∧ Ideal.comap j.toRingHom (I ^ N) ≤ J ^ n) :
    ∃ ι : AdicCompletion J (AddMonoidAlgebra L Q) →ₐ[L] MvPowerSeries (Fin r) L,
      @Continuous _ _
        (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ J n) ⊥)
        I.adicTopology ι ∧
      (∀ b : AddMonoidAlgebra L Q, ι (AdicCompletion.of J _ b) = j b) ∧
      (∀ g : AdicCompletion J (AddMonoidAlgebra L Q) →ₐ[L] MvPowerSeries (Fin r) L,
        @Continuous _ _
          (⨅ n : ℕ, TopologicalSpace.induced (AdicCompletion.evalₐ J n) ⊥)
          I.adicTopology g →
        (∀ b : AddMonoidAlgebra L Q, g (AdicCompletion.of J _ b) = j b) → g = ι) ∧
      Function.Injective ι ∧
      (∀ (x : AdicCompletion J (AddMonoidAlgebra L Q))
          (f : ℕ → AddMonoidAlgebra L Q),
        (∀ n : ℕ, Ideal.Quotient.mk (J ^ n) (f n) = AdicCompletion.evalₐ J n x) →
        (∀ (e : Fin r →₀ ℕ) (c : L),
          (∀ (k n : ℕ), 1 ≤ k → k + e.degree ≤ n →
            c - MvPowerSeries.coeff e (j (f n)) ∈ a ^ k) ↔
          c = MvPowerSeries.coeff e (ι x)) ∧
        (∀ n : ℕ, ι x - j (f n) ∈ I ^ n) ∧
        Filter.Tendsto (fun n : ℕ ↦ AdicCompletion.of J _ (f n)) Filter.atTop
          (@nhds _ (⨅ n : ℕ,
            TopologicalSpace.induced (AdicCompletion.evalₐ J n) ⊥) x)) ∧
      (∀ (n : ℕ) (x : AdicCompletion J (AddMonoidAlgebra L Q)),
        AdicCompletion.evalₐ J n x = 0 → ι x ∈ I ^ n) ∧
      (∀ (x : AdicCompletion J (AddMonoidAlgebra L Q)) (e : Fin r →₀ ℕ),
        e ∉ Q → MvPowerSeries.coeff e (ι x) = 0) ∧
      (⨅ n : ℕ, I ^ n) = ⊥ := by
  sorry

end AddMonoidAlgebra
