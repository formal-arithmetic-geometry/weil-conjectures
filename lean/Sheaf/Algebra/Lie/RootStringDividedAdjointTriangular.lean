module

public import Sheaf.Algebra.Lie.KostantIntegralPBW
public import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.LinearAlgebra.RootSystem.Chain

/-!
# Triangular integral divided adjoints at the bottom of a root string

Source: Milne, Algebraic Groups (2017), Section 23h, Theorem 23.71, pp. 508–509,
for the Chevalley normalization. The local coefficient lemma and its proof are the
agent-written supporting argument in the DAG, rather than a theorem stated by Milne
(blueprint: lem-sfb-root-string-divided-adjoint-triangular).

The enveloping algebra, its generators and its divided powers are the existing constructions.
An arbitrary enumeration of the positive roots specifies their multiplication order. The finite
integer combination is indexed by `Fin t`, including `t = 0` for the empty combination.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open scoped BigOperators

namespace LieAlgebra

/-- At the bottom of an independent positive-root string, the divided adjoint has sign
coefficient, and its action on every positive divided power has the stated integral leading
term and a correction with strictly smaller individual exponents, prescribed weight and cone.
Source: Milne, Algebraic Groups (2017), Section 23h, Theorem 23.71, pp. 508–509,
for the bracket normalization; the local coefficient argument is agent-written
(blueprint: lem-sfb-root-string-divided-adjoint-triangular).

Proof plan:
1. Apply `lem-sfb-root-string-integer-interval` to `a,b`. Since `b-a` is absent, the string
   is `b+ia` for `0 ≤ i ≤ q`. Its successive backward lengths are `i`, so the Chevalley
   brackets give `Y_i = (ad e_a)^i(e_b)/i! = c_i e_(b+ia)`, where `c_0 = 1` and each
   `c_(i+1)` is plus or minus `c_i`. Higher terms vanish. Take `ε = c_k`.
2. Put `X = e_a` in the enveloping algebra and work coefficientwise in formal series.
   The binomial identity gives `E(-t)E(t) = 1` for `E(t) = sum_r X^r t^r/r!`.
   Induction and Pascal's identity give the iterated-commutator binomial formula, hence
   `E(t)uE(-t) = sum_m (ad X)^m(u)t^m/m!`. Cancelling adjacent inverse series gives
   `E(t)e_b^(n)E(-t) = Y(t)^n/n!`, where `Y(t) = sum_(i=0)^q Y_i t^i`.
3. The coefficient of `t^(kn)` is the displayed alternating sum. Expanding `Y(t)^n/n!`
   gives rational words of length `n`, with index sum `kn` and weight `n(b+ka)`.
   Their roots lie in `S = R ∩ {ua+vb : u ≥ 0, v ≥ 1}`. This set is positive and closed
   under root sums that are roots; independence excludes opposite roots and zero sums.
4. Sort these words into the specified order, using `e_r e_s = e_s e_r + [e_r,e_s]`.
   Induct first on length, then on inversions. Swaps lower inversions; bracket corrections
   lower length, preserve weight and remain in `S`. Apply `lem-sfb-rational-pbw` to the
   full ordered Chevalley basis: the rational ordered expansion is unique and has length
   at most `n`. Passing to divided powers changes only its scalar coefficients.
5. In length `n`, only the tuple with every index equal to `k` contributes `e_γ^n`.
   Its coefficient is `ε^n/n!`, giving `ε^n e_γ^(n)`. If some exponent is at least `n`,
   the length bound forces a pure nth power; its weight forces its root to equal `γ`.
   Subtracting the leading term therefore leaves every individual exponent below `n`.
6. Each summand is a product of root divided powers and belongs to the Kostant form.
   Use `lem-sfb-kostant-integral-pbw` in the prescribed order for an integer expansion.
   Its integer independence implies rational independence by clearing denominators.
   Compare with Step 4's positive-only expansion to see that all its coefficients are
   integers and all other triangular coefficients vanish. Subtract `ε^n` and retain the
   weight and cone properties. For `n = 1` the correction is the empty combination. -/
theorem root_string_divided_adjoint_triangular
    (L : Type u) [LieRing L] [LieAlgebra ℚ L] [FiniteDimensional ℚ L]
    [HasTrivialRadical ℚ L] (H : LieSubalgebra ℚ L) [H.IsCartanSubalgebra]
    [LieModule.IsTriangularizable ℚ H L]
    (I : Type v) [Finite I] (P : RootPairing I ℚ (Module.Dual ℚ H) H)
    [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (heval : ∀ (f : Module.Dual ℚ H) (h : H), P.toLinearMap f h = f h)
    (Δ : P.Base) (r N : ℕ) (δ : Fin r ≃ Δ.support)
    (β : Fin N ≃ {i : I // Δ.IsPos i}) (e : I → L)
    (he : ∀ i : I, e i ∈ LieModule.weightSpace L (P.root i) ∧ e i ≠ 0)
    (hopp : ∀ i : I, ⁅e i, e (P.reflectionPerm i i)⁆ = (P.coroot i : L))
    (hadd : ∀ i j l : I, P.root i + P.root j = P.root l →
      ∃ η : ℤ, (η = 1 ∨ η = -1) ∧
        ⁅e i, e j⁆ = ((η : ℚ) * (P.chainBotCoeff i j + 1)) • e l)
    (hzero : ∀ i j : I, P.root i + P.root j ∉ Set.range P.root →
      P.root i + P.root j ≠ 0 → ⁅e i, e j⁆ = 0)
    (B : Module.Basis (Fin r ⊕ I) ℚ L)
    (Bh : ∀ i : Fin r, B (Sum.inl i) = (P.coroot (δ i) : L))
    (Be : ∀ i : I, B (Sum.inr i) = e i)
    (a b : I) (ha : Δ.IsPos a) (hb : Δ.IsPos b)
    (hab : LinearIndependent ℚ ![P.root a, P.root b])
    (hbottom : P.root b - P.root a ∉ Set.range P.root)
    (k : ℕ) (hk : 1 ≤ k) (γ : I) (hγ : P.root γ = P.root b + k • P.root a) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (1 / (k.factorial : ℚ)) • (((ad ℚ L (e a)) ^ k) (e b)) = (ε : ℚ) • e γ ∧
      ∀ n : ℕ, 1 ≤ n →
        ∃ (t : ℕ) (c : Fin t → ℤ) (d : Fin t → Fin N → ℕ),
          (∀ i : Fin t,
            (∀ j : Fin N, d i j < n) ∧
            (∑ j : Fin N, d i j • P.root (β j).val) = n • P.root γ ∧
            (∀ j : Fin N, d i j ≠ 0 → ∃ u v : ℕ,
              1 ≤ v ∧ P.root (β j).val = u • P.root a + v • P.root b)) ∧
          (∑ j ∈ Finset.range (k * n + 1), (-1 : ℤ) ^ j •
            (Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e a)) (k * n - j) *
              Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e b)) n *
              Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e a)) j)) -
            ε ^ n • Algebra.rationalDividedPower (UniversalEnvelopingAlgebra.ι ℚ (e γ)) n =
              ∑ i : Fin t, c i • (List.ofFn (fun j : Fin N ↦
                Algebra.rationalDividedPower
                  (UniversalEnvelopingAlgebra.ι ℚ (e (β j).val)) (d i j))).prod := by
  sorry

end LieAlgebra
