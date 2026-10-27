module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-! # The finite linear dual as a left Hopf module

Source: Zheng, Proposition 4.12(2), printed p. 8; Farnsteiner, Hopf Modules and Integrals:
The Space of Integrals (26 April 2006), printed p. 1.
(blueprint: lem-sfb-finite-dual-hopf-module)

The action is the transpose of multiplication by the antipode. The coaction is uniquely
characterized by evaluation on its final factor. Its compatibility uses the diagonal action,
implemented by swapping the two middle factors before multiplying and acting.
-/

set_option autoImplicit false

@[expose] public section

universe u v w

open scoped TensorProduct

namespace HopfAlgebra

/-- The bilinear action `(h • f)(x) = f(S(h) * x)` on the algebraic linear dual.
This is a concrete composite of linear multiplication, the antipode, and transposition.
Source: Zheng, Proposition 4.12(2), printed p. 8; Farnsteiner, printed p. 1.
(blueprint: lem-sfb-finite-dual-hopf-module) -/
def finiteDualAction (k : Type u) [Field k] (H : Type v) [CommRing H]
    [HopfAlgebra k H] : H →ₗ[k] Module.Dual k H →ₗ[k] Module.Dual k H :=
  Module.Dual.transpose.comp ((LinearMap.mul k H).comp (antipode k))

/-- The finite linear dual, with the antipode action, has a unique evaluation-characterized
left coaction, and these maps satisfy the left Hopf module identities.

Source: Zheng, Proposition 4.12(2), printed p. 8; independently Farnsteiner, Hopf Modules
and Integrals: The Space of Integrals (26 April 2006), printed p. 1.
(blueprint: lem-sfb-finite-dual-hopf-module)

Proof plan from the accepted DAG split:
1. Multiplication by S(h) is linear, so transposition gives the displayed bilinear action.
   The antipode preserves the unit and reverses products; commutativity gives the unit and
   associativity identities for this left action.
2. For the given finite basis e_i, let e_i^* be its coordinate functionals and put
   T_f(x) = (f tensor id)(Delta(x)), using the left tensor unit identification.
   Define rho(f) = sum_i T_f(e_i) tensor e_i^*. Coordinates prove its evaluation formula.
   For any vector space V, z = sum_i (id tensor ev_{e_i})(z) tensor e_i^*, first on pure
   tensors and then by linearity. Thus evaluations detect equality and rho is unique.
   These steps use def-weil-pbc-free-module and def-weil-pbc-module-tensor-product.
3. Evaluating the counit equation at x gives epsilon(T_f(x)) = f(x) by the counit axiom.
4. Evaluating the final dual factor in the coassociativity equation gives on both sides
   sum f(x_1) x_2 tensor x_3, by coassociativity of Delta. Step 2 detects equality.
5. In the convolution algebra Hom_k(H,H tensor H), put j_1(h)=h tensor 1 and
   j_2(h)=1 tensor h. Their product is Delta. Both Delta composed with S and the reversed
   product of j_2 composed with S and j_1 composed with S invert Delta. Uniqueness of
   inverses gives Delta(S(h)) = sum S(h_2) tensor S(h_1). This uses the recorded
   lem-sfb-convolution-linear-map-algebra and algebra-tensor universal-property leaves.
6. Evaluate diagonal compatibility at x. Its right side becomes
   sum h_1 S(h_2) x_2 f(S(h_3) x_1). The antipode and counit axioms give
   sum h_1 S(h_2) tensor S(h_3) = 1 tensor S(h), reducing this expression to
   sum x_2 f(S(h) x_1) = T_{h dot f}(x). Step 2 proves the original tensor equality.
   No cocommutativity, characteristic restriction, or invertibility of S is assumed. -/
theorem finiteDual_hopfModule (k : Type u) [Field k] (H : Type v) [CommRing H]
    [HopfAlgebra k H] (ι : Type w) [Finite ι] (basis : Module.Basis ι k H) :
    (∀ (h : H) (f : Module.Dual k H) (x : H),
      finiteDualAction k H h f x = f (antipode k h * x)) ∧
    (∀ f : Module.Dual k H, finiteDualAction k H 1 f = f) ∧
    (∀ (h h' : H) (f : Module.Dual k H),
      finiteDualAction k H h (finiteDualAction k H h' f) = finiteDualAction k H (h * h') f) ∧
    ∃ ρ : Module.Dual k H →ₗ[k] H ⊗[k] Module.Dual k H,
      (∀ (f : Module.Dual k H) (x : H),
        TensorProduct.rid k H
            ((Module.Dual.eval k H x).lTensor H (ρ f)) =
          TensorProduct.lid k H (f.rTensor H (Coalgebra.comul x))) ∧
      (∀ ρ' : Module.Dual k H →ₗ[k] H ⊗[k] Module.Dual k H,
        (∀ (f : Module.Dual k H) (x : H),
          TensorProduct.rid k H
              ((Module.Dual.eval k H x).lTensor H (ρ' f)) =
            TensorProduct.lid k H (f.rTensor H (Coalgebra.comul x))) → ρ' = ρ) ∧
      (∀ f : Module.Dual k H,
        TensorProduct.assoc k H H (Module.Dual k H)
            ((Coalgebra.comul : H →ₗ[k] H ⊗[k] H).rTensor (Module.Dual k H) (ρ f)) =
          ρ.lTensor H (ρ f)) ∧
      (∀ f : Module.Dual k H,
        TensorProduct.lid k (Module.Dual k H)
          ((Coalgebra.counit : H →ₗ[k] k).rTensor (Module.Dual k H) (ρ f)) = f) ∧
      (∀ (h : H) (f : Module.Dual k H),
        ρ (finiteDualAction k H h f) =
          TensorProduct.map (LinearMap.mul' k H) (TensorProduct.lift (finiteDualAction k H))
            (TensorProduct.tensorTensorTensorComm k H H H (Module.Dual k H)
              (Coalgebra.comul h ⊗ₜ[k] ρ f))) := by
  sorry

end HopfAlgebra
