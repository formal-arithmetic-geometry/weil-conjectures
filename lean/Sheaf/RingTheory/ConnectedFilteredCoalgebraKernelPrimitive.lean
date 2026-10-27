module

public import Mathlib.RingTheory.Coalgebra.Basic
import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Primitive elements in kernels from connected filtered coalgebras

Source: Milne, Algebraic Groups (2017), Definition 14.4 and equation (91), printed
p.281, and Lemma 14.43, printed p.294, coproduct calculation. This general coalgebra
lemma is an agent-written consequence of those structures, not Lemma 14.44.
(blueprint: lem-sfb-connected-filtered-coalgebra-kernel-primitive)
-/

set_option autoImplicit false

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra

/-- A noninjective counital coalgebra map out of a coalgebra with an exhaustive
connected increasing filtration has a nonzero primitive element in its kernel.
The tensor subspaces in the filtration condition are the ranges of the tensor
products of the two subspace inclusions; their finite supremum is their sum.

Source: Milne, Algebraic Groups (2017), Definition 14.4 and equation (91), printed
p.281, and Lemma 14.43, printed p.294, coproduct calculation; agent-written general
coalgebra kernel lemma.
(blueprint: lem-sfb-connected-filtered-coalgebra-kernel-primitive)

Proof: (1) Choose the least n for which F n meets ker f nontrivially and choose
nonzero x in that intersection. Counit preservation implies epsilon(x)=0. If n=0,
x=a*g and epsilon(g)=1 force a=0, a contradiction. Thus n is positive. Minimality
makes the restriction h of f to L=F(n-1) injective.
(2) Put p(y)=y-epsilon(y)*g. It kills F 0 and preserves each F i. The two counit
identities give (p tensor p)Delta(x)=Delta(x)-g tensor x-x tensor g=:r. Apply this
map to the filtration sum. Its endpoint summands vanish; every interior summand
lands in the image of L tensor L. Hence r=(iota tensor iota)(t) for some t in
L tensor L. This only uses the image interpretation of the tensor subspaces from
 def-weil-pbc-module-tensor-product, not injectivity of their inclusions.
(3) The coalgebra-map equation and f(x)=0 give (f tensor f)(r)=0. Functoriality on
pure tensors then gives (h tensor h)(t)=0.
(4) Use lem-sfb-vector-space-tensor-family-zero-detection with the singleton
family h. For s=(h tensor id_L)(t), the previous equation gives
(id_D tensor h)(s)=0. Flip the tensor factors, apply zero detection with right
factor D, and flip back to obtain s=0. Apply zero detection once more with right
factor L to get t=0. Consequently r=0 and Delta(x)=x tensor g+g tensor x, proving
all the claimed clauses. -/
theorem exists_primitive_mem_ker_of_not_injective
    {k : Type u} [Field k]
    {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    {D : Type w} [AddCommGroup D] [Module k D] [Coalgebra k D]
    (g : C) (hg_comul : comul (R := k) g = g ⊗ₜ[k] g)
    (hg_counit : counit (R := k) g = 1)
    (F : ℕ → Submodule k C) (hF_mono : Monotone F)
    (hF_zero : F 0 = Submodule.span k {g})
    (hF_exhaustive : ∀ x : C, ∃ n : ℕ, x ∈ F n)
    (hF_comul : ∀ n : ℕ, (F n).map (comul (R := k) (A := C)) ≤
      ⨆ i ∈ Finset.range (n + 1),
        LinearMap.range (TensorProduct.map (F i).subtype (F (n - i)).subtype))
    (f : C →ₗ[k] D)
    (hf_comul : comul (R := k) (A := D) ∘ₗ f =
      TensorProduct.map f f ∘ₗ comul (R := k) (A := C))
    (hf_counit : counit (R := k) (A := D) ∘ₗ f = counit (R := k) (A := C))
    (hf : ¬ Function.Injective f) :
    ∃ x : C, x ≠ 0 ∧ f x = 0 ∧ counit (R := k) x = 0 ∧
      comul (R := k) x = x ⊗ₜ[k] g + g ⊗ₜ[k] x := by
  sorry

end Coalgebra
