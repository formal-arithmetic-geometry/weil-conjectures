module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # The coefficient coalgebra of a finite-dimensional comodule

Source: Milne, Algebraic Groups (2017), §9(d), printed pp.174–175, immediately
before Theorem 9.32. (blueprint: lem-sfb-finite-comodule-coefficient-coalgebra)

The coefficients are extracted by the coordinate functionals of the given basis.
Their span has the restricted coalgebra structure, with the tensor inclusion
explicitly asserted to be injective.
-/

set_option autoImplicit false

@[expose] public section

universe u v w t

open scoped TensorProduct

namespace Coalgebra

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C]
variable {M : Type w} [AddCommGroup M] [Module k M]
variable {I : Type t}

/-- The coefficient c_ij is obtained by applying the i-th coordinate functional to
rho(e_j), then using k tensor C = C. This is an actual linear construction.
Source: Milne, Algebraic Groups, §9(d), printed p.174.
(blueprint: lem-sfb-finite-comodule-coefficient-coalgebra) -/
noncomputable def matrixCoefficient (b : Module.Basis I k M) (ρ : M →ₗ[k] M ⊗[k] C)
    (i j : I) : C :=
  TensorProduct.lid k C ((b.coord i).rTensor C (ρ (b j)))

/-- The subspace spanned by all matrix coefficients, including the empty span.
Source: Milne, Algebraic Groups, §9(d), printed p.175, the subcoalgebra C_V.
(blueprint: lem-sfb-finite-comodule-coefficient-coalgebra) -/
def coefficientSpan (b : Module.Basis I k M) (ρ : M →ₗ[k] M ⊗[k] C) : Submodule k C :=
  Submodule.span k (Set.range fun ij : I × I => matrixCoefficient b ρ ij.1 ij.2)

/-- The matrix coefficients of a finite-dimensional right comodule span a
finite-dimensional subcoalgebra, with the ambient comultiplication and counit.
Source: Milne, Algebraic Groups, §9(d), printed pp.174–175, before Theorem 9.32.
(blueprint: lem-sfb-finite-comodule-coefficient-coalgebra)

Proof: (1) Apply the coordinate functional e_i^* to the first tensor factor.
The universal property of def-weil-pbc-module-tensor-product gives the extraction
map T_i, used in matrixCoefficient. Expanding vectors in the basis and using that
pure tensors span proves rho(e_j) = sum_i e_i tensor c_ij and uniqueness.
(2) Evaluate comodule coassociativity at e_j and extract its i-th coordinate.
The two sides become sum_a c_ia tensor c_aj and Delta(c_ij).
(3) Evaluate the comodule counit at e_j and apply e_i^* to get epsilon(c_ij)=delta_ij.
(4) I times I is finite, so the coefficient span is finite-dimensional in the sense
of def-weil-finite-dimensional-subspace; the empty span is zero.
(5) By lem-trf-vector-subspace-complement choose a complement of this span D in C.
Projection p onto D retracts the inclusion iota. Tensor functoriality from
 def-weil-pbc-module-tensor-product makes p tensor p and its threefold analogue
left inverses to the tensor inclusions, proving their injectivity.
(6) Set Delta_D = (p tensor p) Delta iota and epsilon_D = epsilon iota.
The coefficient identity proves (iota tensor iota) Delta_D = Delta iota first on
the spanning coefficients, then on D, so these maps are the restrictions.
(7) Apply the injective threefold tensor inclusion to coassociativity on D and
cancel using coassociativity on C. Apply iota to each counit identity and cancel.
The restriction equations are exactly the coalgebra-homomorphism conditions.
For I empty, D is zero and the same equations are equations between zero maps. -/
theorem finite_comodule_coefficient_coalgebra [Coalgebra k C] [FiniteDimensional k M]
    [Fintype I] [DecidableEq I] (b : Module.Basis I k M) (ρ : M →ₗ[k] M ⊗[k] C)
    (hcoassoc : (TensorProduct.assoc k M C C).toLinearMap ∘ₗ ρ.rTensor C ∘ₗ ρ =
      (Coalgebra.comul (R := k) (A := C)).lTensor M ∘ₗ ρ)
    (hcounit : (TensorProduct.rid k M).toLinearMap ∘ₗ
      (Coalgebra.counit (R := k) (A := C)).lTensor M ∘ₗ ρ = LinearMap.id) :
    (∀ j : I, ρ (b j) = ∑ i : I, b i ⊗ₜ[k] matrixCoefficient b ρ i j) ∧
    (∀ i j : I, Coalgebra.comul (R := k) (matrixCoefficient b ρ i j) =
      ∑ a : I, matrixCoefficient b ρ i a ⊗ₜ[k] matrixCoefficient b ρ a j) ∧
    (∀ i j : I, Coalgebra.counit (R := k) (matrixCoefficient b ρ i j) =
      if i = j then 1 else 0) ∧
    FiniteDimensional k (coefficientSpan b ρ) ∧
    Function.Injective
      (TensorProduct.map (coefficientSpan b ρ).subtype (coefficientSpan b ρ).subtype) ∧
    ∃ d : Coalgebra k (coefficientSpan b ρ),
      TensorProduct.map (coefficientSpan b ρ).subtype (coefficientSpan b ρ).subtype ∘ₗ
          d.comul = Coalgebra.comul (R := k) ∘ₗ (coefficientSpan b ρ).subtype ∧
      d.counit = Coalgebra.counit (R := k) ∘ₗ (coefficientSpan b ρ).subtype := by
  sorry

end Coalgebra
