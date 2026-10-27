module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Contraction
import Mathlib.LinearAlgebra.Dual.BaseChange

/-! # Finite coalgebra duality and scalar extension

Source: Milne, Algebraic Groups (2017), §9(d), printed pp.174–175;
equation (77), printed p.237, and Theorem 12.18(c)⇒(d), printed p.238.
(blueprint: lem-sfb-finite-coalgebra-dual-base-change)

The dual algebra is Mathlib's `WithConv (Module.Dual k D)`, with its convolution
ring and algebra instances. The coalgebra on `F ⊗[k] D` is Mathlib's scalar-extended
coalgebra from `Mathlib.RingTheory.Coalgebra.TensorProduct`, publicly imported
by the convolution module. Every equivalence below is specified by its actual
values, so the statement identifies the canonical evaluation and scalar comparison.
-/

set_option autoImplicit false

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra

/-- Finite coalgebra duality, the evaluation character correspondence, and the
convolution algebra comparison under any field extension, including the zero coalgebra.
Source: Milne, Algebraic Groups (2017), §9(d), printed pp.174–175;
equation (77), printed p.237, and Theorem 12.18(c)⇒(d), printed p.238.
(blueprint: lem-sfb-finite-coalgebra-dual-base-change)

Proof:
1. By lem-weil-pbc-vector-space-free, choose a basis of D. Finitely many generators
have coordinates in a common finite set of basis indices, so that basis is finite.
By lem-weil-pbc-vector-space-projective and lem-sf-finite-projective-dual, the dual
is finite-dimensional and evaluation is a linear isomorphism. Apply
lem-sfb-convolution-linear-map-algebra to (k,D,k): the convolution multiplication
is multiplication in k after the tensor of the functionals after comultiplication,
and the unit is the counit. No cocommutativity is used.
2. Evaluation at a group-like x is multiplicative, since Delta(x) = x tensor x;
it preserves the unit since epsilon(x) = 1, and sends c epsilon to c. It is linear,
so it is a unital k-algebra homomorphism.
3. Conversely, a character is evaluation at a unique x by biduality. Preservation
of the unit gives epsilon(x) = 1. Multiplicativity makes every product functional
vanish on Delta(x) - x tensor x. By lem-sfb-finite-free-tensor-dual and generation
by pure tensors (def-weil-pbc-module-tensor-product), all functionals vanish there.
By lem-weil-pbc-vector-space-dual-separates the difference is zero. This proves
the character bijection, with precisely the asserted evaluation formula.
4. The dual clause of lem-trf-projective-exterior-scalar-comparisons gives the
F-linear scalar comparison, since D is finite free. On pure tensors it sends
a tensor f to the functional b tensor x mapped to abf(x). The scalar-extended
counit sends b tensor x to b epsilon(x), and if Delta(x) = sum u_i tensor v_i,
its comultiplication sends b tensor x to sum (b tensor u_i) tensor (1 tensor v_i).
Tensor balancing makes these maps well-defined. Coassociativity and both counit
laws follow on pure tensors from those on D, and tensor generation extends them
to every input. Thus lem-sfb-convolution-linear-map-algebra also gives the target
convolution algebra.
5. On a tensor f, c tensor g, and b tensor x, both the scalar comparison of the
product and the convolution of the comparisons evaluate to
acb sum_i f(u_i)g(v_i). Commutation is used only in F. Bilinearity and pure tensor
generation extend this identity to all inputs. The unit 1 tensor epsilon maps to
the extended counit; F-linearity gives compatibility with scalars. Hence the
linear comparison is a unital F-algebra isomorphism.
6. For D = 0 both duals and scalar extensions are zero, and the linear and algebra
comparisons are the unique isomorphisms. There are no group-like elements and no
unital homomorphisms from the zero algebra to the field k, so the character
bijection is between empty types. All preceding steps allow the empty basis. -/
theorem finite_dual_baseChange
    {k : Type u} [Field k] {D : Type v} [AddCommGroup D] [Module k D]
    [Coalgebra k D] [FiniteDimensional k D]
    (F : Type w) [Field F] [Algebra k F] :
    FiniteDimensional k (WithConv (Module.Dual k D)) ∧
    (∃ e : D ≃ₗ[k] Module.Dual k (WithConv (Module.Dual k D)),
      ∀ (x : D) (f : WithConv (Module.Dual k D)), e x f = f x) ∧
    (∃ c : {x : D // IsGroupLikeElem k x} ≃ (WithConv (Module.Dual k D) →ₐ[k] k),
      ∀ (x : {x : D // IsGroupLikeElem k x}) (f : WithConv (Module.Dual k D)),
        c x f = f x.val) ∧
    (∃ θ : F ⊗[k] WithConv (Module.Dual k D) ≃ₐ[F]
        WithConv (Module.Dual F (F ⊗[k] D)),
      ∀ (a b : F) (f : WithConv (Module.Dual k D)) (x : D),
        θ (a ⊗ₜ[k] f) (b ⊗ₜ[k] x) = a * b * algebraMap k F (f x)) := by
  sorry

end Coalgebra
