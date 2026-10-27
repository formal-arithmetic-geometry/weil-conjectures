module

public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Sheaf.RingTheory.FiniteComoduleCoefficientCoalgebra

/-! # Finite subsets lie in finite-dimensional subcoalgebras

Source: Milne, Algebraic Groups (2017), Proposition 4.7, printed p.86;
§9(d), printed pp.174–175; Theorem 12.18(c)⇒(d), printed p.238.
(blueprint: lem-sfb-coalgebra-finite-subcoalgebra)

The tensor inclusion is injective, and the two restriction equations say precisely
that the subspace inclusion preserves comultiplication and counit.
-/

set_option autoImplicit false

@[expose] public section

universe u v

namespace Coalgebra

/-- Every finite subset of a coalgebra over a field lies in a finite-dimensional
subcoalgebra, with the restricted comultiplication and counit.
Source: Milne, Algebraic Groups (2017), Proposition 4.7, printed p.86;
§9(d), printed pp.174–175; Theorem 12.18(c)⇒(d), printed p.238.
(blueprint: lem-sfb-coalgebra-finite-subcoalgebra)

Proof: Regard C as a right C-comodule with coaction its comultiplication.
Coassociativity and the right counit law give the comodule identities.
By lem-sfb-comodule-finite-subcomodule, choose a finite-dimensional subcomodule
V containing S, with coaction rho_V and equivariant inclusion into C.
Choose a finite basis (e_i) of V. By lem-sfb-finite-comodule-coefficient-coalgebra,
write Delta(e_j) = sum_i e_i tensor c_ij and let D be the span of these coefficients.
That lemma gives finite dimension, injectivity of the tensor inclusion, and a
coalgebra structure on D whose maps restrict the ambient maps.
Applying epsilon tensor id to the displayed expansion and using the left counit
law gives e_j = sum_i epsilon(e_i) c_ij. Thus each basis vector belongs to D,
so V is contained in D and S is contained in D. Tensor maps and the tensor unit
identification are those of def-weil-pbc-module-tensor-product. The restriction
equations are exactly the coalgebra-homomorphism conditions on the inclusion.
If V is zero, its basis and its coefficients are empty, and D is zero. Hence the
argument includes the empty subset and the zero coalgebra. No cocommutativity
or finite-dimensionality hypothesis on C is used. -/
theorem exists_finiteDimensional_subcoalgebra
    {k : Type u} [Field k] {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]
    (S : Set C) (hS : S.Finite) :
    ∃ D : Submodule k C, S ⊆ D ∧ FiniteDimensional k D ∧
      Function.Injective (TensorProduct.map D.subtype D.subtype) ∧
      ∃ d : Coalgebra k D,
        TensorProduct.map D.subtype D.subtype ∘ₗ d.comul =
          Coalgebra.comul (R := k) ∘ₗ D.subtype ∧
        d.counit = Coalgebra.counit (R := k) ∘ₗ D.subtype := by
  sorry

end Coalgebra
