module

public import Sheaf.Algebra.Lie.KostantIntegralForm
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.LinearAlgebra.RootSystem.Base

/-!
# Integral lower-degree commutators of nonopposite root divided powers

Source: Milne, Algebraic Groups (2017), Section 23h, Theorem 23.71, pp. 508–509,
for the Chevalley-basis normalization. The divided-power identity is the agent-written
formal coefficient argument recorded in the DAG, not a theorem stated there by Milne
(blueprint: lem-sfb-chevalley-rank-two-straightening).

Words are lists of root indices and positive natural exponents, retaining multiplication
order in the tensor-algebra quotient. The finite integer linear combination may be empty.
-/

@[expose] public section

universe u v

namespace LieAlgebra

/-- Nonopposite root divided powers commute modulo integral words of strictly lower degree,
with every word in the positive cone of the two roots and of the prescribed total weight.
Source: Milne, Algebraic Groups (2017), Section 23h, Theorem 23.71, pp. 508–509,
for the assumed bracket table; the supporting divided-power calculation is agent-written
(blueprint: lem-sfb-chevalley-rank-two-straightening).

Proof plan:
1. If either exponent is zero, the divided power is one, so use the empty linear combination.
   Otherwise apply `lem-sfb-chevalley-string-central-parity` to order the two roots as `(a,b)`.
   Interchanging them negates the commutator and preserves its degree, cone and weight.
   Write `Y_k = (ad e_a)^k(e_b)/k!`, with string length `q`, integral coefficients `c_k`,
   and central correction terms `C_d = z_d e_(2b+da)` as supplied by that node. These bracket
   identities hold in the enveloping algebra because its relations are `xy-yx = [x,y]`.
2. Work coefficientwise in `U[[s,t]]`. Set `E_gamma(w) = sum_j w^j e_gamma^j/j!` for a
   series `w` with zero constant term. Induction using Pascal's identity gives
   `(ad x)^k(y) = sum_i (-1)^i choose(k,i) x^(k-i) y x^i`. Consequently
   `E_a(s) e_b E_a(-s) = sum_(k=0)^q s^k Y_k`. The coefficient in positive degree `k`
   of `E_a(s) E_a(-s)` is `e_a^k (1-1)^k/k!`, so these series are inverse. Conjugation
   preserves products, hence `E_a(s) E_b(t) = exp(t sum_k s^k Y_k) E_a(s)`.
3. Apply `lem-sfb-formal-class-two-exponential` to `Z_(k+1) = t s^k Y_k`. Triple
   brackets vanish by `lem-sfb-chevalley-string-central-parity`, giving
   `E_b(t) (prod_(k=1)^q E_(b+ka)(c_k s^k t))`
   `* (prod_(d=1)^(2q) E_(2b+da)(-z_d s^d t^2)) * E_a(s)`, omitting nonroots.
   The first product is in increasing `k` and the second in increasing `d`. Each bracket
   `[Y_i,Y_j]` commutes with every `Y_k`, hence also with their products and brackets.
   Thus the `C_d` commute mutually; a second application of the same formal factorization
   splits the correction exponential. Zero corrections contribute one.
4. Extract the coefficient of `s^M t^N`. If the outer exponents are `u,v` and the inner
   ones are `A_k,B_d`, they satisfy `M = v + sum k A_k + sum d B_d` and
   `N = u + sum A_k + 2 sum B_d`. There are finitely many choices, all with integral
   coefficient `prod c_k^A_k prod (-z_d)^B_d`. The unique term with all inner exponents
   zero is `e_b^(N) e_a^(M)`; subtract it. Every remaining word has degree
   `D = u+v+sum A_k+sum B_d`, with `M+N-D = sum k A_k + sum (d+1) B_d > 0`.
   Its weight is `M a+N b` and each root is in the nonnegative integral cone of `a,b`.
   Omit zero-exponent factors, combine repeated words, and restore the original sign. -/
theorem chevalley_dividedPower_commutator_lower_degree
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
    (α β : I) (hne : α ≠ β) (hnopp : P.root α ≠ -P.root β) (m n : ℕ) :
    (∃ (t : ℕ) (c : Fin t → ℤ) (w : Fin t → List (I × ℕ)),
      (∀ i : Fin t,
        (∀ d ∈ w i, 1 ≤ d.2 ∧ ∃ p q : ℕ, P.root d.1 = p • P.root α + q • P.root β) ∧
        ((w i).map Prod.snd).sum < m + n ∧
        ((w i).map (fun d ↦ d.2 • P.root d.1)).sum = m • P.root α + n • P.root β) ∧
      Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e α)) m *
          Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e β)) n -
        Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e β)) n *
          Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e α)) m =
        ∑ i : Fin t, c i • ((w i).map (fun d ↦ Algebra.rationalDividedPower
          (UniversalEnvelopingAlgebra.ι ℚ (e d.1)) d.2)).prod) ∧
    ((m = 0 ∨ n = 0) →
      Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e α)) m *
          Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e β)) n -
        Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e β)) n *
          Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e α)) m = 0) := by
  sorry

end LieAlgebra
