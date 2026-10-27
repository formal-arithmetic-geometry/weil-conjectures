module

public import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.VectorSpace
import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Detection of subcomodules and comodule maps by the convolution dual

Source: Milne, Algebraic Groups (2017), Chapter 9(d), printed pp.174–175,
and Example 9.36, printed p.178. The general contraction-detection argument
is supplied by the DAG proof, without a dimension or cocommutativity restriction.
(blueprint: lem-sfb-coalgebra-dual-action-detection)

## Main definitions and statements

- `Coalgebra.dualContraction`: the operator `(1 tensor f) rho` on a coaction.
- `Coalgebra.dual_action_detection`: the convolution action, subspace detection,
  uniqueness and identities of the restricted coaction, and detection of maps.
-/

set_option autoImplicit false

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Coalgebra

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C]
variable {M : Type w} [AddCommGroup M] [Module k M]

/-- Contraction of a right coaction by a linear functional, using the canonical
identification of `M tensor k` with `M`. This uses actual tensor maps.
Source: Milne, Algebraic Groups, Chapter 9(d), printed pp.174–175;
Example 9.36, printed p.178.
(blueprint: lem-sfb-coalgebra-dual-action-detection) -/
noncomputable def dualContraction (ρ : M →ₗ[k] M ⊗[k] C) (f : C →ₗ[k] k) :
    Module.End k M :=
  (_root_.TensorProduct.rid k M).toLinearMap ∘ₗ f.lTensor M ∘ₗ ρ

/-- The convolution dual acts on every right comodule and detects its subcomodules
and comodule morphisms. Any linear map satisfying the inclusion equation is the
unique such map (uniqueness holds for every subspace, without assuming stability)
and automatically satisfies both laws.
Source: Milne, Algebraic Groups, Chapter 9(d), printed pp.174–175;
Example 9.36, printed p.178; general detection argument in the DAG proof.
(blueprint: lem-sfb-coalgebra-dual-action-detection)

Proof:
1. Write rho(m) as a finite sum m_i tensor c_i. Tensor bilinearity gives linearity
   in f. Contract coassociativity by 1 tensor f tensor g to obtain
   T_f(T_g(m)) = T_(f*g)(m), in that order. The counit gives T_epsilon = id,
   hence T_(a epsilon) = a id. With lem-sfb-convolution-linear-map-algebra
   these are all the algebra-homomorphism laws.
2. Contractions detect zero in X tensor C: flip a tensor and apply
   lem-sfb-vector-space-tensor-family-zero-detection to the family of all
   functionals C -> k, which detects zero by
   lem-weil-pbc-vector-space-dual-separates. The flip and unit identifications
   are those of def-weil-pbc-module-tensor-product.
3. By lem-trf-vector-subspace-complement choose a complement to W and let p be
   projection onto W, with p i = id. Set r = id - i p; then r i = 0 and its
   kernel is i(W). For every D, p tensor id_D retracts i tensor id_D, so the
   latter is injective, by tensor generation and functoriality.
4. Stability implies that every contraction of (r tensor id_C) rho(i w) is zero;
   step 2 makes it zero. Define rho_W = (p tensor id_C) rho i. Then its tensor
   inclusion is rho i. Conversely, this factorization implies stability after
   contraction. Applying p tensor id_C to any factorization forces this formula,
   proving uniqueness among all linear maps with the factorization.
5. Apply i to the counit expression on W, use the factorization and the counit
   on M, and cancel i using p. For coassociativity apply i tensor id_C tensor id_C,
   use the factorization twice on one side and once on the other, then use
   coassociativity on M and cancel the tensor inclusion using step 3.
   The canonical associativity identifications agree on pure tensors.
6. For u : M -> N, the contraction of
   d = (u tensor id_C) rho_M - rho_N u is u T_f - T_f u, by pure tensors.
   Thus d = 0 implies all intertwining identities, and conversely those
   identities imply d(m) = 0 for every m by step 2. This uses the full dual,
   so no finite-dimensionality assumption is needed, including for zero spaces. -/
theorem dual_action_detection [Coalgebra k C]
    (ρM : M →ₗ[k] M ⊗[k] C)
    (hcoassocM : (_root_.TensorProduct.assoc k M C C).toLinearMap ∘ₗ ρM.rTensor C ∘ₗ ρM =
      (Coalgebra.comul (R := k) (A := C)).lTensor M ∘ₗ ρM)
    (hcounitM : (_root_.TensorProduct.rid k M).toLinearMap ∘ₗ
      (Coalgebra.counit (R := k) (A := C)).lTensor M ∘ₗ ρM = LinearMap.id) :
    (∃ T : WithConv (C →ₗ[k] k) →ₐ[k] Module.End k M,
      ∀ f : WithConv (C →ₗ[k] k), T f = dualContraction ρM f.ofConv) ∧
    (∀ f g : WithConv (C →ₗ[k] k),
      dualContraction ρM (f * g).ofConv =
        (dualContraction ρM f.ofConv).comp (dualContraction ρM g.ofConv)) ∧
    (∀ a : k, dualContraction ρM (a • Coalgebra.counit (R := k) (A := C)) =
      a • (LinearMap.id : Module.End k M)) ∧
    (∀ W : Submodule k M,
      (∀ (f : C →ₗ[k] k) (m : M), m ∈ W → dualContraction ρM f m ∈ W) ↔
        ∃ ρW : W →ₗ[k] W ⊗[k] C, W.subtype.rTensor C ∘ₗ ρW = ρM ∘ₗ W.subtype) ∧
    (∀ (W : Submodule k M) (ρW : W →ₗ[k] W ⊗[k] C),
      W.subtype.rTensor C ∘ₗ ρW = ρM ∘ₗ W.subtype →
        (∀ ρW' : W →ₗ[k] W ⊗[k] C,
          W.subtype.rTensor C ∘ₗ ρW' = ρM ∘ₗ W.subtype → ρW' = ρW) ∧
        (_root_.TensorProduct.assoc k W C C).toLinearMap ∘ₗ ρW.rTensor C ∘ₗ ρW =
          (Coalgebra.comul (R := k) (A := C)).lTensor W ∘ₗ ρW ∧
        (_root_.TensorProduct.rid k W).toLinearMap ∘ₗ
          (Coalgebra.counit (R := k) (A := C)).lTensor W ∘ₗ ρW = LinearMap.id) ∧
    (∀ (N : Type z) [AddCommGroup N] [Module k N] (ρN : N →ₗ[k] N ⊗[k] C),
      (_root_.TensorProduct.assoc k N C C).toLinearMap ∘ₗ ρN.rTensor C ∘ₗ ρN =
        (Coalgebra.comul (R := k) (A := C)).lTensor N ∘ₗ ρN →
      (_root_.TensorProduct.rid k N).toLinearMap ∘ₗ
        (Coalgebra.counit (R := k) (A := C)).lTensor N ∘ₗ ρN = LinearMap.id →
      ∀ u : M →ₗ[k] N, u.rTensor C ∘ₗ ρM = ρN ∘ₗ u ↔
        ∀ f : C →ₗ[k] k, u ∘ₗ dualContraction ρM f = dualContraction ρN f ∘ₗ u) := by
  sorry

end Coalgebra
