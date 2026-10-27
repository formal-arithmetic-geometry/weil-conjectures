module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.Data.Nat.Choose.Sum

/-!
# Pointwise exponential of a locally nilpotent Lie derivation

Source: Milne, Algebraic Groups (2017), Theorem 23.63, first proof, pp. 503–504,
and the characteristic-zero extension on p. 508. This is an agent-supplied
prerequisite for the Serre reflection construction, not a theorem stated by Milne.
(blueprint: lem-sfb-locally-nilpotent-derivation-exponential)
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace Module.End

/-- A locally nilpotent rational Lie derivation exponentiates pointwise to a Lie
algebra automorphism. Every positive annihilating cutoff gives its value by the
finite exponential sum; the same formula for the negative derivation gives its inverse.

Source: the agent-supplied prerequisite for Milne, Algebraic Groups (2017),
Theorem 23.63, first proof, pp. 503–504, with characteristic-zero extension p. 508.
(blueprint: lem-sfb-locally-nilpotent-derivation-exponential)

Proof plan:
1. Once a power kills a vector, all higher powers kill it. Enlarge two cutoffs to
   their maximum to prove independence. Use a common cutoff for two vectors to
   prove linearity. Induction gives (-D)^n x = (-1)^n D^n x, so -D is locally nilpotent.
2. Package D as a LieDerivation and apply LieDerivation.iterate_apply_lie'
   (lem-sfb-lie-derivation-iterate-binomial). If D^r x = D^s y = 0, each term of
   D^(r+s) [x,y] vanishes, giving an annihilating cutoff for the bracket.
3. Expand at that cutoff. The coefficient choose(n,i)/n! is 1/(i!(n-i)!). Reindex
   by j = n-i; terms with i >= r or j >= s vanish and all remaining pairs occur
   exactly once. Bilinearity from def-wf-lie-algebra identifies the result with
   [Exp_D x, Exp_D y].
4. If D^N x = 0, the same power kills both exponential images. Expand both
   composites with cutoff N. Terms of degree k >= N vanish. For k < N the
   coefficient is sum_i choose(k,i)(-1)^i/k!. By add_pow
   (lem-pur-commutative-ring-binomial-expansion), this is zero for k > 0 and
   one for k = 0. Thus both composites are the identity, giving the asserted
   Lie equivalence and the inverse formula at every valid cutoff. -/
theorem exists_lieEquiv_of_locallyNilpotent_derivation
    {L : Type u} [LieRing L] [LieAlgebra ℚ L] (D : Module.End ℚ L)
    (hder : ∀ x y : L, D ⁅x, y⁆ = ⁅D x, y⁆ + ⁅x, D y⁆)
    (hnil : ∀ x : L, ∃ N : ℕ, 1 ≤ N ∧ (D ^ N) x = 0) :
    ∃ e : L ≃ₗ⁅ℚ⁆ L,
      (∀ (x : L) (N : ℕ), 1 ≤ N → (D ^ N) x = 0 →
        e x = ∑ n ∈ Finset.range N, ((n.factorial : ℚ)⁻¹) • ((D ^ n) x)) ∧
      (∀ (x : L) (N : ℕ), 1 ≤ N → ((-D) ^ N) x = 0 →
        e.symm x = ∑ n ∈ Finset.range N, ((n.factorial : ℚ)⁻¹) • (((-D) ^ n) x)) := by
  sorry

end Module.End
