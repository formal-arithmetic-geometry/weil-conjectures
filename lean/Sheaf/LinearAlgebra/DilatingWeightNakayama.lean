module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Logic.Function.Iterate

/-! # Generation modulo a weight-dilating semilinear operator

Source: independent graded refinement supporting Milne, Algebraic Groups (2017),
Proposition 14.50, printed p.296. The refinement itself is not stated in Milne.
(blueprint: lem-sfb-dilating-weight-nakayama)
-/

@[expose] public section

universe u v

namespace LinearMap

/-- Homogeneous lifts spanning the quotient by the span of a weight-dilating
semilinear operator generate the whole space under its iterates.

Source: independent agent refinement supporting Milne, Algebraic Groups (2017),
Proposition 14.50, printed p.296, and the homogeneous Frobenius-module argument.
This graded assertion is not a statement of that proposition.
(blueprint: lem-sfb-dilating-weight-nakayama)

Proof:
1. Let W be the span of all iterates of the b_j. It contains the b_j and is
   T-stable: applying T to a finite linear combination replaces each coefficient
   a by sigma(a) and each iterate by the next. No surjectivity of sigma is used.
2. The internal direct sum gives linear component projections pi_nu. Multiplication
   by p is injective on the integral lattice, so the nu-component of T(v) is
   T(pi_mu(v)) if nu = p * mu, and is zero if no such mu exists.
3. For x in the nu-component, lift the quotient-spanning expression to write
   x = sum_j c_j b_j + sum_i a_i T(v_i). Project onto nu. Only b_j of weight nu
   survive, and the second sum vanishes unless nu = p * mu; in that case it becomes
   sum_i a_i T(pi_mu(v_i)). These are arbitrary scalar multiples, so sigma need
   not be invertible.
4. Define d(nu) as the sum of absolute values of its integer coordinates.
   If nu = p * mu is nonzero, then d(nu) = p * d(mu) > d(mu), because p >= 2.
5. Strong induction on d(nu) proves that every component lies in W. The zero
   component vanishes by hypothesis. A weight outside p times the lattice is
   handled by the first sum in step 3. Otherwise the predecessor components lie
   in W by induction, and their images lie in W by step 1.
6. Every vector is a finite sum of components, so W is the whole space. For s = 0
   the only component is zero; for m = 0 the same induction has empty b_j-sums.
   Thus both cases, and the zero space, are included. -/
theorem span_iterates_eq_top_of_dilating_weights
    {k : Type u} [Field k] {V : Type v} [AddCommGroup V] [Module k V]
    (σ : k →+* k) (p : ℤ) (hp : 2 ≤ p) (s : ℕ)
    (A : (Fin s → ℤ) → Submodule k V) (hA : DirectSum.IsInternal A)
    (hzero : A 0 = ⊥) (T : V →ₛₗ[σ] V)
    (hT : ∀ (ν : Fin s → ℤ) (x : V), x ∈ A ν → T x ∈ A (p • ν))
    (m : ℕ) (b : Fin m → V) (νb : Fin m → (Fin s → ℤ))
    (hb : ∀ j : Fin m, b j ∈ A (νb j))
    (hspan : Submodule.span k
      (Set.range fun j : Fin m ↦ (Submodule.span k (Set.range T)).mkQ (b j)) = ⊤) :
    Submodule.span k (Set.range fun rj : ℕ × Fin m ↦
      (T : V → V)^[rj.1] (b rj.2)) = ⊤ := by
  sorry

end LinearMap
