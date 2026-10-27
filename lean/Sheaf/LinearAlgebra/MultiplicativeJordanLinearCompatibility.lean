/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil SHEAF project
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Multiplicative Jordan decomposition and linear and tensor compatibility

Source: Milne, Algebraic Groups (2017), Theorem 9.11 and Propositions 9.13 and 9.15,
printed pp. 168–169 (blueprint: lem-sfb-multiplicative-jordan-linear-compatibility).

The decomposition predicate records precisely the commuting factorization, an eigenbasis,
and a positive power killing the unipotent part minus the identity. Compatibility is stated
for arbitrary decompositions, so uniqueness identifies these with the parts of each map.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace LinearEquiv

/-- The multiplicative Jordan factorization conditions from Milne, Algebraic Groups (2017),
Theorem 9.11, printed p. 168, in the algebraically closed specialization
(blueprint: lem-sfb-multiplicative-jordan-linear-compatibility).
The factors are invertible by their type. Diagonalizability is an explicit finite eigenbasis;
the nilpotence exponent is positive, including when the vector space is zero. -/
def IsMultiplicativeJordanDecomposition {K : Type u} [Field K]
    {V : Type v} [AddCommGroup V] [Module K V] (A S U : V ≃ₗ[K] V) : Prop :=
  A = S * U ∧ A = U * S ∧
    (∃ (n : ℕ) (b : Module.Basis (Fin n) K V) (a : Fin n → K),
      ∀ i : Fin n, S (b i) = a i • b i) ∧
    ∃ N : ℕ, 1 ≤ N ∧ (U.toLinearMap - LinearMap.id) ^ N = 0

/-- Existence and uniqueness of the multiplicative Jordan factors, Milne, Algebraic Groups
(2017), Theorem 9.11, printed pp. 168–169
(blueprint: lem-sfb-multiplicative-jordan-linear-compatibility).

Proof: use `lem-sfb-generalized-eigenspace-direct-sum` to write `V` as its primary direct sum.
The zero-eigenvalue primary space vanishes because `A` is invertible. On the primary space
of eigenvalue `a`, define `S` by scalar multiplication by `a` and its inverse by `a⁻¹`.
The direct sum makes these maps well defined and inverse; concatenating bases gives an
`S`-eigenbasis. Set `U = S⁻¹ A`. On each primary space, `U - 1 = a⁻¹ (A - a)`, so its
`max 1 (dim V)`-th power vanishes. Both factors commute and multiply to `A`.
For uniqueness, an eigenvector of any competing `S'` of eigenvalue `a` belongs to the
`a`-primary space of `A`, since there `A - a = a (U' - 1)`. Thus `S` and `S'` agree on an
entire basis, and cancellation recovers `U = U'`. For `V = 0`, both factors are the unique
identity automorphism, the eigenbasis is empty, and exponent one suffices. -/
theorem existsUnique_multiplicativeJordanDecomposition {K : Type u} [Field K] [IsAlgClosed K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (A : V ≃ₗ[K] V) :
    ∃! p : (V ≃ₗ[K] V) × (V ≃ₗ[K] V), IsMultiplicativeJordanDecomposition A p.1 p.2 := by
  sorry

/-- Linear intertwiners preserve both Jordan parts, Milne, Algebraic Groups (2017),
Proposition 9.13, printed p. 169
(blueprint: lem-sfb-multiplicative-jordan-linear-compatibility).

Proof: the identity `f A = B f` gives `(B - a)^n f = f (A - a)^n` by induction on `n`.
Hence `f` carries every `a`-primary space of `A` into that of `B`, using
`lem-sfb-generalized-eigenspace-direct-sum`. The construction and uniqueness from the
preceding theorem show that both semisimple parts act by `a` on these spaces. The
semisimple intertwiner identity therefore holds on their direct sum, which is all of `V`.
Multiplying by the two semisimple inverses gives `f S_A⁻¹ = S_B⁻¹ f`; substituting
`U_A = S_A⁻¹ A` and `U_B = S_B⁻¹ B` gives the unipotent intertwiner identity. -/
theorem multiplicativeJordanDecomposition_intertwines {K : Type u} [Field K] [IsAlgClosed K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {A S U : V ≃ₗ[K] V} {B T Z : W ≃ₗ[K] W}
    (hA : IsMultiplicativeJordanDecomposition A S U)
    (hB : IsMultiplicativeJordanDecomposition B T Z)
    (f : V →ₗ[K] W) (hf : f.comp A.toLinearMap = B.toLinearMap.comp f) :
    f.comp S.toLinearMap = T.toLinearMap.comp f ∧
      f.comp U.toLinearMap = Z.toLinearMap.comp f := by
  sorry

/-- Tensor products preserve both Jordan parts, Milne, Algebraic Groups (2017),
Proposition 9.15, printed p. 169
(blueprint: lem-sfb-multiplicative-jordan-linear-compatibility).

Proof: tensor products of finite bases give finite dimensionality; `A⁻¹ ⊗ B⁻¹` is the
inverse of `A ⊗ B`, by evaluation on pure tensors. For primary vectors of eigenvalues
`a,b`, put `X = (A - a) ⊗ B` and `Y = a ⊗ (B - b)`. On the span of these pure tensors,
`X` and `Y` commute, `A ⊗ B - ab = X + Y`, and `X^d = Y^e = 0` for
`d = max 1 (dim V)` and `e = max 1 (dim W)`, by
`lem-sfb-generalized-eigenspace-direct-sum`. Expanding `(X + Y)^(d+e)` shows that it
vanishes: each monomial has either at least `d` factors `X` or at least `e` factors `Y`.
This uses no division and works in every characteristic. Thus these tensors lie in the
`ab`-primary space of `A ⊗ B`. Its semisimple part and `S ⊗ T` both act there by `ab`.
Primary expansions in each factor and bilinearity show that these subspaces span the
tensor space, proving equality of semisimple parts. Recovering the unipotent parts as
semisimple inverse times the original map proves their equality. Uniqueness makes this
true for any decomposition of the tensor automorphism. A zero factor gives the zero
tensor space and its unique automorphism. -/
theorem multiplicativeJordanDecomposition_tensor {K : Type u} [Field K] [IsAlgClosed K]
    {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {W : Type w} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    {A S U : V ≃ₗ[K] V} {B T Z : W ≃ₗ[K] W}
    {P Q : TensorProduct K V W ≃ₗ[K] TensorProduct K V W}
    (hA : IsMultiplicativeJordanDecomposition A S U)
    (hB : IsMultiplicativeJordanDecomposition B T Z)
    (hC : IsMultiplicativeJordanDecomposition (TensorProduct.congr A B) P Q) :
    P = TensorProduct.congr S T ∧ Q = TensorProduct.congr U Z := by
  sorry

end LinearEquiv
