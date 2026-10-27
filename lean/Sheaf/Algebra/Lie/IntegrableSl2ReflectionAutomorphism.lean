module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Weights.Basic
public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Reflection from a locally nilpotent rational sl2 action

Source: Milne, Algebraic Groups (2017), Theorem 23.63, first proof, pp.503--504,
and the rational-field extension on p.508. The pointwise exponential argument
is the agent-supplied expansion recorded in the DAG.
(blueprint: lem-sfb-integrable-sl2-reflection-automorphism)

The three exponentials are written directly as `finsum`s. Local nilpotence
makes each sum finite at each vector, without a uniform nilpotence bound.
Weight spaces are Mathlib's ordinary `LieModule.weightSpace`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace LieAlgebra

/-- The pointwise exponential reflection and its restriction to every weight space.
Source: Milne, Algebraic Groups (2017), Theorem 23.63, pp.503--504, and p.508;
agent-supplied locally nilpotent expansion of the reflection input.
(blueprint: lem-sfb-integrable-sl2-reflection-automorphism)

Proof plan:
1. Jacobi makes E = ad e and G = -ad f derivations. Local nilpotence of ad f
   implies that of G, since G^n x = (-1)^n (ad f)^n x. Apply
   lem-sfb-locally-nilpotent-derivation-exponential to obtain automorphisms
   A = exp E and B = exp G, with inverses exp(-E) and exp(-G). Hence w = ABA
   is a rational Lie automorphism. The sums here are precisely their pointwise
   finite sums: every term past an annihilating exponent vanishes.
2. For t in T and a = alpha(t), the relations give Et = -a e, Ee = 0,
   Ef = h, Eh = -2e, Gt = -a f, Ge = h, Gf = 0, Gh = -2f.
   Thus A(t) = t-a e, A(e) = e, A(f) = f+h-e, A(h) = h-2e;
   B(t) = t-a f, B(e) = e+h-f, B(f) = f, B(h) = h-2f.
   Indeed E^2 f = -2e, G^2 e = -2f, and subsequent terms vanish.
3. Composing gives BA(t) = t-a e-a h and ABA(t) = t-a h.
   Also A(B(A(e))) = A(e+h-f) = -f and A(B(A(f))) = A(-e) = -e.
   In particular w(h) = -h.
4. The map s(t) = t-alpha(t)h on T is an involution, since alpha(h) = 2.
   Both w and its inverse restrict to s. For x of weight beta,
   [t,w(x)] = w([s(t),x]) = (beta(t)-beta(h)alpha(t))w(x).
5. Put gamma = beta-beta(h)alpha. For y of weight gamma and z = w^{-1}(y),
   [t,z] = w^{-1}([w(t),y]) = gamma(s(t))z = beta(t)z,
   since gamma(h) = -beta(h). The restrictions of w and its inverse are
   inverse rational linear maps on the indicated ordinary weight spaces.
   This includes zero weight spaces and uses no weight-space decomposition.
-/
theorem exists_integrableSl2_reflectionAutomorphism
    (L : Type u) [LieRing L] [LieAlgebra ℚ L]
    (T : LieSubalgebra ℚ L) [IsLieAbelian T]
    (h : T) (e f : L) (α : T →ₗ[ℚ] ℚ)
    (hα : α h = 2) (hef : ⁅e, f⁆ = (h : L))
    (hte : ∀ t : T, ⁅(t : L), e⁆ = α t • e)
    (htf : ∀ t : T, ⁅(t : L), f⁆ = -(α t) • f)
    (hne : ∀ x : L, ∃ n : ℕ, 0 < n ∧ (ad ℚ L e ^ n) x = 0)
    (hnf : ∀ x : L, ∃ n : ℕ, 0 < n ∧ (ad ℚ L f ^ n) x = 0) :
    ∃ w : L ≃ₗ⁅ℚ⁆ L,
      (⇑w =
        (fun x : L ↦ ∑ᶠ n : ℕ, (n.factorial : ℚ)⁻¹ • (ad ℚ L e ^ n) x) ∘
        (fun x : L ↦ ∑ᶠ n : ℕ, (n.factorial : ℚ)⁻¹ • ((-ad ℚ L f) ^ n) x) ∘
        (fun x : L ↦ ∑ᶠ n : ℕ, (n.factorial : ℚ)⁻¹ • (ad ℚ L e ^ n) x)) ∧
      (∀ t : T, w (t : L) = (t : L) - α t • (h : L)) ∧
      w e = -f ∧ w f = -e ∧
      ∀ β : T →ₗ[ℚ] ℚ,
        ∃ φ : LieModule.weightSpace L (fun t : T ↦ β t) ≃ₗ[ℚ]
            LieModule.weightSpace L (fun t : T ↦ β t - β h * α t),
          ∀ x : LieModule.weightSpace L (fun t : T ↦ β t),
            (φ x : L) = w (x : L) := by
  sorry

end LieAlgebra
