module

public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.LinearAlgebra.RootSystem.Base
public import Mathlib.Data.Nat.Choose.Basic

/-!
# Central root-string brackets and integral half-sums

Source: Milne, Algebraic Groups (2017), Appendix C, section g, table (180) and the four
rank-two diagrams, printed pp. 621–622; Section 23h, Theorem 23.71, pp. 508–509
(blueprint: lem-sfb-chevalley-string-central-parity).

The centrality and parity conclusion is the agent-written finite root-coordinate calculation
recorded in the DAG, rather than a theorem explicitly stated in Milne. All operations here
are in the Lie algebra; there is no assertion about its enveloping algebra.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace LieAlgebra

/-- Orienting a pair of distinct nonopposite roots makes its divided adjoint string have
central pairwise brackets and integral grouped half-sums.

Source: Milne, Algebraic Groups (2017), Appendix C, section g, table (180) and the four
rank-two diagrams, printed pp. 621–622; Section 23h, Theorem 23.71, pp. 508–509
(blueprint: lem-sfb-chevalley-string-central-parity).

Proof plan:
1. Reducedness makes the two roots rationally independent. Intersect the root system with
   their rational plane. It is finite, spanning, reduced and crystallographic: restrict
   the coroot functionals and reflections to the plane. Apply
   `lem-sfb-rank-two-root-coordinate-classification` to obtain the four coordinate lists.
2. Use squared lengths x²+y², x²-xy+y², x²-2xy+2y², x²-3xy+3y² in types A1×A1, A2,
   B2, G2 respectively, and put the shorter of the prescribed roots first. Checking all
   signed coordinate pairs, excluding equal and opposite roots, gives these (p,q):
   A1×A1: (0,0); A2: (1,0),(0,1); B2: (0,0),(2,0),(0,2),(1,1);
   G2: (1,0),(3,0),(0,0),(0,1),(0,3),(2,1),(1,2).
   The roots b+ka occur exactly for -p ≤ k ≤ q, so p+q ≤ 3.
3. For r_k=b+ka the backward string length is p+k. Repeated use of the assumed
   Chevalley bracket formula gives Y_k=c_k e_(r_k), with coefficient the product of k
   signs times (p+1)...(p+k)/k!, hence absolute value choose(p+k,k). At k=q the next
   bracket vanishes by the zero-bracket rule. All higher iterated adjoints vanish too.
4. Check the same coordinate lists for r_i+r_j with i<j. The only root sums are in G2:
   (p,q)=(0,3), (i,j)=(0,3), backward length 0, sum 2b+3a;
   (p,q)=(0,3), (i,j)=(1,2), backward length 2, sum 2b+3a;
   (p,q)=(1,2), (i,j)=(0,1), backward length 2, sum 2b+a.
   For the first two rows 3b+(3+k)a is absent for 0 ≤ k ≤ 3; for the last row
   3b+(1+k)a is absent for 0 ≤ k ≤ 2. Independence excludes zero weights.
5. The zero-bracket rule kills every omitted pair and every bracket of a listed sum
   with another r_k. Alternation kills diagonal pairs; skew-symmetry handles reversed
   pairs. Bilinearity therefore gives all the asserted triple-bracket vanishings.
6. For (p,q)=(0,3), all |c_k| are one. The two contributions to C_3 have coefficients
   of absolute values one and three; their half-sum (±1±3)/2 is integral. For (1,2),
   the |c_k| are (1,2,3), so the sole bracket has absolute coefficient 1·2·3=6,
   and C_1 has coefficient ±3. Every other C_d is zero. If its weight is not a root,
   each summand vanishes; if the weight is a root but the sum is empty, take z_d=0.
   For q=0 the degree range is empty. The zeroth adjoint power gives Y_0=e_b. -/
theorem chevalley_string_central_parity
    (L : Type u) [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
    [HasTrivialRadical ℚ L] (H : LieSubalgebra ℚ L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable ℚ H L]
    (I : Type v) [Finite I] (P : RootPairing I ℚ (Module.Dual ℚ H) H)
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (heval : ∀ (f : Module.Dual ℚ H) (h : H), P.toLinearMap f h = f h)
    (Δ : P.Base) (e : I → L)
    (he : ∀ i : I, e i ∈ LieModule.weightSpace L (P.root i) ∧ e i ≠ 0)
    (hopp : ∀ i : I, ⁅e i, e (P.reflectionPerm i i)⁆ = (P.coroot i : L))
    (hadd : ∀ i j k : I, P.root i + P.root j = P.root k →
      ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
        ⁅e i, e j⁆ = ((ε : ℚ) * (P.chainBotCoeff i j + 1)) • e k)
    (hzero : ∀ i j : I, P.root i + P.root j ∉ Set.range P.root →
      P.root i + P.root j ≠ 0 → ⁅e i, e j⁆ = 0)
    (B : Module.Basis (Δ.support ⊕ I) ℚ L)
    (Bh : ∀ i : Δ.support, B (Sum.inl i) = (P.coroot i : L))
    (Be : ∀ i : I, B (Sum.inr i) = e i)
    (α β : I) (hne : α ≠ β) (hnopp : P.root α ≠ -P.root β) :
    ∃ a b : I,
      ((a = α ∧ b = β) ∨ (a = β ∧ b = α)) ∧
      LinearIndependent ℚ ![P.root a, P.root b] ∧
      let p := P.chainBotCoeff a b
      let q := P.chainTopCoeff a b
      let Y : ℕ → L := fun k ↦ ((k.factorial : ℚ)⁻¹) • ((ad ℚ L (e a)) ^ k) (e b)
      let C : ℕ → L := fun d ↦ (1 / 2 : ℚ) •
        ∑ i ∈ Finset.range (q + 1),
          ∑ j ∈ (Finset.range (q + 1)).filter (fun j ↦ i < j ∧ i + j = d), ⁅Y i, Y j⁆
      p + q ≤ 3 ∧
      Y 0 = e b ∧
      (∀ k : ℕ, q < k → Y k = 0) ∧
      (∀ k : ℕ, k ≤ q → ∃ (r : I) (c : ℤ),
        P.root r = P.root b + k • P.root a ∧
        Y k = (c : ℚ) • e r ∧ c.natAbs = (p + k).choose k) ∧
      (∀ i j k : ℕ, i ≤ q → j ≤ q → k ≤ q → ⁅⁅Y i, Y j⁆, Y k⁆ = 0) ∧
      (∀ d : ℕ, 1 ≤ d → d ≤ 2 * q →
        (2 • P.root b + d • P.root a ∉ Set.range P.root → C d = 0) ∧
        (∀ r : I, P.root r = 2 • P.root b + d • P.root a →
          ∃ z : ℤ, C d = (z : ℚ) • e r)) := by
  sorry

end LieAlgebra
