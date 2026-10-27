module

public import WeilConjectures.RingTheory.PthRootAlgebraLocal
import Sheaf.RingTheory.ParameterRootAlgebra
public import Mathlib.RingTheory.Coalgebra.Convolution
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.Nat.Choose.Sum

/-! # Top-coordinate convolution pairing

Source: the agent algebra lemma supporting Milne, Algebraic Groups (2017), Chapter 10;
convolution conventions in §9(d), printed p.174.
(blueprint: lem-sfb-truncated-coordinate-convolution-pairing)
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct BigOperators
namespace Algebra

/-- Evaluation of convolution at the highest bounded monomial is nondegenerate on both sides.
The quotient `pthRootAlgebra (p ^ r) n F 0` is the polynomial quotient by coordinate powers.
The convolution evaluation is expanded using `LinearMap.convMul_apply`; no coalgebra instance
is chosen in the statement, so the supplied algebra maps retain the canonical scalar action.

Source: agent highest-total-degree argument for the algebra input to the finite-coordinate
version of Milne, Algebraic Groups (2017), Chapter 10; §9(d), printed p.174 gives the convolution
convention. This is not asserted to be a theorem stated in Milne.
(blueprint: lem-sfb-truncated-coordinate-convolution-pairing)

Proof plan:
1. Apply `Algebra.ParameterRoot.exists_basis` to the zero tuple and exponent `q = p ^ r`.
Its bounded monomials `e_α` form a basis. Write `u_α` for their coefficient functionals.
2. The pure tensors `e_α ⊗ e_β` form a basis: they span by tensor bilinearity and are separated
by the coefficient maps induced by `(f,g) ↦ u_α(f) * u_β(g)`. Products add exponents or vanish,
so quotient relations never lower the degree of a nonzero monomial.
3. The counit kills every nonconstant monomial. The two counit identities therefore force
`Δ(t_i) = t_i ⊗ 1 + 1 ⊗ t_i + R_i`, where each monomial in `R_i` has positive degree in
both tensor factors, hence total degree at least two. No symmetry is used.
4. Iterated Frobenius gives `(1 + Z) ^ q = 1 + Z ^ q`. Multiplying the binomial expansion
of `(1 + Z) ^ (q - 1)` by `1 + Z` and comparing coefficients gives
`choose (q - 1) j = (-1) ^ j` in `F`, for `j < q`; all these coefficients are nonzero.
5. Put `ν = (q - 1,...,q - 1)` and `N = n * (q - 1)`. Multiplicativity of `Δ` shows that
`Δ(∏ i, t_i ^ (q - 1))` has no terms of total degree below `N`. Its degree-`N` part is
`∏ i, (t_i ⊗ 1 + 1 ⊗ t_i) ^ (q - 1)`. Thus the coefficient at `(α,β)` of total degree `N`
is zero unless `α + β = ν`, when it is `(-1) ^ |α|`.
6. For nonzero `b`, choose a maximal-degree `β` with `b(e_β) ≠ 0`, and set `α = ν - β`.
Evaluation of `u_α * b` at the top monomial is `(-1) ^ |α| * b(e_β) ≠ 0`: lower-degree
terms vanish by step 5, higher-degree support vanishes by maximality, and only `β` remains
in its degree. Interchanging the roles of the two tensor coordinates similarly detects
any nonzero `a` using `a * u_β`. Take contrapositives. With no variables the basis has one
empty monomial, the top product is `1`, and the calculation is multiplication in `F`. -/
theorem truncatedCoordinate_convolution_pairing_nondegenerate
    (F : Type u) [Field F] (p r n : ℕ) [Fact p.Prime] [CharP F p] (hr : 1 ≤ r)
    (Δ : pthRootAlgebra (p ^ r) n F 0 →ₐ[F]
      pthRootAlgebra (p ^ r) n F 0 ⊗[F] pthRootAlgebra (p ^ r) n F 0)
    (ε : pthRootAlgebra (p ^ r) n F 0 →ₐ[F] F)
    (hε : ∀ i : Fin n, ε (Ideal.Quotient.mk _ (MvPolynomial.X i)) = 0)
    (hcoassoc : ∀ x : pthRootAlgebra (p ^ r) n F 0,
      _root_.TensorProduct.assoc F (pthRootAlgebra (p ^ r) n F 0)
        (pthRootAlgebra (p ^ r) n F 0) (pthRootAlgebra (p ^ r) n F 0)
        (Δ.toLinearMap.rTensor _ (Δ x)) = Δ.toLinearMap.lTensor _ (Δ x))
    (hleft : ∀ x : pthRootAlgebra (p ^ r) n F 0,
      _root_.TensorProduct.lid F _ (ε.toLinearMap.rTensor _ (Δ x)) = x)
    (hright : ∀ x : pthRootAlgebra (p ^ r) n F 0,
      _root_.TensorProduct.rid F _ (ε.toLinearMap.lTensor _ (Δ x)) = x) :
    (∀ b : pthRootAlgebra (p ^ r) n F 0 →ₗ[F] F,
      (∀ a : pthRootAlgebra (p ^ r) n F 0 →ₗ[F] F,
        LinearMap.mul' F F (_root_.TensorProduct.map a b
          (Δ (∏ i : Fin n, Ideal.Quotient.mk _ (MvPolynomial.X i) ^ (p ^ r - 1)))) = 0) →
        b = 0) ∧
    (∀ a : pthRootAlgebra (p ^ r) n F 0 →ₗ[F] F,
      (∀ b : pthRootAlgebra (p ^ r) n F 0 →ₗ[F] F,
        LinearMap.mul' F F (_root_.TensorProduct.map a b
          (Δ (∏ i : Fin n, Ideal.Quotient.mk _ (MvPolynomial.X i) ^ (p ^ r - 1)))) = 0) →
        a = 0) := by
  sorry

end Algebra
