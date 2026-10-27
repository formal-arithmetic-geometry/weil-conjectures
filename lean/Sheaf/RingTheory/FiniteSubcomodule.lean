module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Finite subsets lie in finite-dimensional subcomodules

Source: Milne, Algebraic Groups (2017), Proposition 4.7, printed p.86, and
§9(d), printed p.174. The coefficient proof uses only the coalgebra identities.
(blueprint: lem-sfb-comodule-finite-subcomodule)
-/

set_option autoImplicit false

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Coalgebra

/-- Every finite subset of a right coalgebra comodule lies in a finite-dimensional
subcomodule, with its coaction and the inclusion equation explicitly supplied.
Source: Milne, Algebraic Groups (2017), Proposition 4.7, printed p.86;
coalgebra and comodule definitions in §9(d), printed p.174.
(blueprint: lem-sfb-comodule-finite-subcomodule)

Proof:
1. By lem-weil-pbc-vector-space-basis-through-vector choose a basis (e_j) of C.
   Expand each rho(t), for t in T, as a finite sum of m_tj tensor e_j, using
   def-weil-pbc-module-tensor-product. The coordinate functionals lambda_j
   identify m_tj with the contraction (1 tensor lambda_j) rho(t).
2. Coassociativity and contraction in the third factor by lambda_l give
   rho(m_tl) = sum_j m_tj tensor d_jl, where d_jl = (1 tensor lambda_l) Delta(e_j).
   This is Milne's coefficient identity (26), in right-comodule order.
3. Let V be the span of all these finitely many m_tj. It is finite-dimensional
   by def-weil-finite-dimensional-subspace. Counitality expresses each t as
   sum_j epsilon(e_j) m_tj, so T is contained in V. The coefficient identity
   implies rho(i(V)) lies in the image of i tensor 1_C, by linearity.
4. Extend a basis of V to a basis of M by
   lem-weil-pbc-vector-space-basis-through-vector, and define the linear
   retraction p of i by zero on the extra basis vectors. Tensor functoriality
   from def-weil-pbc-module-tensor-product gives a left inverse p tensor 1_D
   to i tensor 1_D for every D. Set rho_V = (p tensor 1_C) rho i. The image
   containment in step 3 proves (i tensor 1_C) rho_V = rho i.
5. Compose the two coassociativity expressions for rho_V with the injective
   threefold tensor inclusion. Tensor functoriality and the inclusion equation
   turn them into the two equal expressions for rho i; cancel the inclusion.
   Similarly, compose the counit expression with i and cancel its injectivity.
   For T empty take V = 0; this also covers M = 0. Neither multiplication on C
   nor cocommutativity is used. -/
theorem exists_finiteDimensional_subcomodule
    {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C]
    [Coalgebra k C] {M : Type w} [AddCommGroup M] [Module k M]
    (ρ : M →ₗ[k] M ⊗[k] C)
    (hcoassoc : (TensorProduct.assoc k M C C).toLinearMap ∘ₗ ρ.rTensor C ∘ₗ ρ =
      (Coalgebra.comul (R := k) (A := C)).lTensor M ∘ₗ ρ)
    (hcounit : (TensorProduct.rid k M).toLinearMap ∘ₗ
      (Coalgebra.counit (R := k) (A := C)).lTensor M ∘ₗ ρ = LinearMap.id)
    (T : Set M) (hT : T.Finite) :
    ∃ V : Submodule k M, FiniteDimensional k V ∧ T ⊆ V ∧
      ∃ ρV : V →ₗ[k] V ⊗[k] C,
        (TensorProduct.assoc k V C C).toLinearMap ∘ₗ ρV.rTensor C ∘ₗ ρV =
          (Coalgebra.comul (R := k) (A := C)).lTensor V ∘ₗ ρV ∧
        (TensorProduct.rid k V).toLinearMap ∘ₗ
          (Coalgebra.counit (R := k) (A := C)).lTensor V ∘ₗ ρV = LinearMap.id ∧
        V.subtype.rTensor C ∘ₗ ρV = ρ ∘ₗ V.subtype := by
  sorry

end Coalgebra
