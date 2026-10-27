module

public import Sheaf.RingTheory.FormalInitialDiagram
public import Mathlib.RingTheory.MvPowerSeries.Order
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Continuous supported division from homogeneous division

Source: Bierstone--Milman, Invent. Math. 128 (1997), Lemma 7.3, Corollary 7.4,
and Lemma 7.5, p.263; ILO VIII 2.3.11--2.3.13 provide the resolution context.
(blueprint: lem-trf-homogeneous-continuous-formal-division)

The vertex index type may be any finite ordered set, including a degree prefix
with its inherited order and the empty set. Each such family has its own basis
hypothesis, diagram, and quotient supports. No prefix hypothesis is inferred from
that of the whole family. All topologies below are explicitly the variable-adic
ones; no topology on the coefficient field is assumed.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace MonomialDiagram

/-- Homogeneous indexed bases give unique continuous supported formal division and
its finite-jet dimension criterion.

Source: Bierstone--Milman, Lemma 7.3, Corollary 7.4, Lemma 7.5, p.263; supporting
context ILO VIII 2.3.11--2.3.13.
(blueprint: lem-trf-homogeneous-continuous-formal-division)

Proof plan (the sixteen steps of the node):
1. The coefficient-family definition and finite convolution show that membership
   in the t-th power of the variable ideal means vanishing below degree t.
   Group each exponent above degree t by a fixed subexponent of degree t.
   Degree-bounded sets are finite, including when there are no variables.
2. Take coordinates in the assumed degree-k indexed basis and group them by
   vertex and by the complementary monomials. This gives unique homogeneous
   quotients u(i,k) and remainder v(k), with u(i,k)=0 when k<d(i).
3. Recursively set E(0)=g and E(k+1)=E(k)-sum_i u(i,k)f(i)-v(k).
   Maintain E(k) in the k-th power and the identity obtained by subtracting all
   earlier corrections from g.
4. The convolution formula and the order of f(i)-H(i) show that the correction
   has exactly the degree-k component of E(k). Both invariants follow.
5. Define quotient and remainder coefficients using u(i,degree(beta)+d(i))
   and v(degree(gamma)). These are actual coefficient families, with the stated
   supports, without needing any infinite-sum existence theorem.
6. Through degree N only corrections of weight at most N contribute. The
   recursion identity therefore gives the division identity coefficientwise.
7. Subtract two supported divisions. A nonzero difference has a least weight;
   its homogeneous equation contradicts independence of that indexed basis.
8. Add divisions and multiply them by scalars. Uniqueness gives L-linearity.
9. If g vanishes below t, every correction of weight less than t is zero.
   The quotients vanish below max(0,t-d(i)) and the remainder below t.
10. These bounds, applied to differences, give continuity for the adic
    filtrations, using input exponent a+d(i) for quotient output exponent a.
11. Supported sums are precisely the kernel of the remainder. A nonzero
    remainder coefficient of degree b stays nonzero on the coset modulo the
    (b+1)-st power, proving that this linear subspace is closed.
12. Complementary monomials through degree t span the truncated quotient by
    division and truncation. Delete dependent images to obtain a finite basis;
    apply lem-sfb-independent-family-spanning-cardinality for the dimension bound.
13. Equality of these dimensions forces the finite-jet spanning map to be
    injective: a nontrivial relation would remove one spanning vector and give
    a strictly smaller dimension. The zero-dimensional case is immediate.
14. If equality holds in every degree, truncate the remainder of an element
    of I. Its truncation lies in that kernel and hence is zero in every degree.
15. Conversely, if r kills I, its identity on supported remainders and its
    order estimate show that the finite-jet spanning map is injective. Its
    monomial images are a basis, so the Hilbert functions agree.
16. The same proof applies to every finite ordered degree prefix satisfying
    its own basis hypothesis. For an empty family r=id and the kernel is zero;
    the Hilbert criterion becomes I=0. With no variables, only degree zero
    remains, and a nonempty distinct family has one nonzero scalar divisor.
-/
theorem exists_continuous_supported_formal_division
    {L : Type u} [Field L] {n : ℕ} {ι : Type} [Fintype ι] [LinearOrder ι]
    (α : ι → Fin n →₀ ℕ) (hα : Function.Injective α)
    (f : ι → MvPowerSeries (Fin n) L)
    (horder : ∀ i : ι, (f i).order = ((α i).degree : ℕ∞))
    (hbasis : ∀ t : ℕ,
      LinearIndependent L (divisionFamily (generated α) α
        (fun i ↦ MvPowerSeries.truncTotal ((α i).degree + 1)
          (MvPowerSeries.homogeneousComponent (α i).degree (f i))) t) ∧
      SpansDegree (generated α) α
        (fun i ↦ MvPowerSeries.truncTotal ((α i).degree + 1)
          (MvPowerSeries.homogeneousComponent (α i).degree (f i))) t) :
    ∃ (q : ι → MvPowerSeries (Fin n) L →ₗ[L] MvPowerSeries (Fin n) L)
      (r : MvPowerSeries (Fin n) L →ₗ[L] MvPowerSeries (Fin n) L),
      (∀ g : MvPowerSeries (Fin n) L,
        g = (∑ i : ι, q i g * f i) + r g ∧
        (∀ i : ι, Function.support (q i g) ⊆ quotientSupport α i) ∧
        Function.support (r g) ⊆ (generated α)ᶜ ∧
        ∀ (a : ι → MvPowerSeries (Fin n) L) (b : MvPowerSeries (Fin n) L),
          g = (∑ i : ι, a i * f i) + b →
          (∀ i : ι, Function.support (a i) ⊆ quotientSupport α i) →
          Function.support b ⊆ (generated α)ᶜ →
          a = (fun i ↦ q i g) ∧ b = r g) ∧
      (∀ i : ι, @Continuous _ _
        (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L)))).adicTopology
        (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L)))).adicTopology
        (q i)) ∧
      @Continuous _ _
        (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L)))).adicTopology
        (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L)))).adicTopology r ∧
      (∀ (t : ℕ) (g : MvPowerSeries (Fin n) L),
        g ∈ (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L)))) ^ t →
        (∀ i : ι, q i g ∈
          (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L)))) ^
            (t - (α i).degree)) ∧
        r g ∈ (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L)))) ^ t) ∧
      {g : MvPowerSeries (Fin n) L | ∃ a : ι → MvPowerSeries (Fin n) L,
        (∀ i : ι, Function.support (a i) ⊆ quotientSupport α i) ∧
        g = ∑ i : ι, a i * f i} = (LinearMap.ker r : Set (MvPowerSeries (Fin n) L)) ∧
      @IsClosed _
        (Ideal.span (Set.range (MvPowerSeries.X (σ := Fin n) (R := L)))).adicTopology
        (LinearMap.ker r : Set (MvPowerSeries (Fin n) L)) ∧
      (∀ I : Ideal (MvPowerSeries (Fin n) L), (∀ i : ι, f i ∈ I) →
        (∀ t : ℕ, FiniteDimensional L (truncation I t)) ∧
        (∀ t : ℕ, Module.finrank L (truncation I t) ≤ hilbertCount (generated α) t) ∧
        ((∀ t : ℕ, Module.finrank L (truncation I t) = hilbertCount (generated α) t) ↔
          ∀ g ∈ I, r g = 0)) := by
  sorry

end MonomialDiagram
