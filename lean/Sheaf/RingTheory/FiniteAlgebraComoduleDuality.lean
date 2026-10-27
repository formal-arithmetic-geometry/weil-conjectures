module

public import Sheaf.RingTheory.FiniteAlgebraDualityData
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Contraction

/-! # Finite algebras and right comodules of their duals

Source: Milne, Algebraic Groups (2017), §9(d), pp.174--175, paragraph after Lemma 9.35,
Example 9.36, and 9.41--9.42, pp.177--180.
(blueprint: lem-sfb-finite-algebra-comodule-duality)

Actions are algebra homomorphisms to the endomorphism algebra. The two bundled categories
in the data module retain the actual finite-dimensional vector spaces and intertwining linear maps.
No nontriviality assumption is imposed on the algebra or the vector spaces.
-/

set_option autoImplicit false

@[expose] public section

universe u v w t

open CategoryTheory
open scoped TensorProduct

namespace FiniteAlgebraComoduleDuality

variable {k : Type u} [Field k]
variable {E : Type v} [Ring E] [Algebra k E]

/-- The unique dual coalgebra and the complete left-action/right-coaction dictionary,
including both formulas, every finite basis, morphisms and the equivalence over vector spaces.
Source: Milne, §9(d), pp.174--175, paragraph after Lemma 9.35, Example 9.36, and
9.41--9.42, pp.177--180. (blueprint: lem-sfb-finite-algebra-comodule-duality)

Proof:
1. Use lem-weil-pbc-vector-space-free to choose a basis. A finite spanning family has
finitely many basis supports, whose union contains every basis index. The coordinate
functionals form the dual basis, since d = sum_i d(a_i) a_i^*.
2. By lem-sc-tensor-product-free-basis, double and triple tensors of dual basis vectors
are bases. Evaluation at basis vectors therefore detects equality. In M tensor E^*,
every tensor is uniquely sum_i m_i tensor a_i^*, with m_i obtained by contraction.
3. By lem-sfb-finite-free-tensor-dual, transpose multiplication through dualDistribEquiv
to define Delta; define epsilon(d)=d(1). The tensor universal property
(def-weil-pbc-module-tensor-product) gives linearity and the displayed pairing.
Evaluations detect uniqueness, so the construction is independent of a basis.
4. Evaluate the two coassociativity sides at a,b,c to obtain d((ab)c) and d(a(bc)).
Evaluate the counit sides at a to obtain d(1a) and d(a1). Associativity and the unit
laws in E prove all the coalgebra axioms, without commutativity of E.
5. From an action form rho(m)=sum_i (a_i m) tensor a_i^*. Contraction at a returns
am. Contraction at a,b on the two coalgebra factors gives a(bm) and (ab)m, proving
coassociativity; contraction at 1 proves the counit law.
6. Conversely contraction of rho at a is linear in a and m. The counit gives the unit
law, and contracting the coassociativity identity gives a(bm)=(ab)m.
7. The contraction formula recovers the original action. The unique tensor normal
form in step 2 recovers the original coaction. This also proves independence of every
choice of finite basis, and hence the asserted equivalences of structure sets.
8. For a k-linear f, contraction of rho_N f - (f tensor id) rho_M at a is
 a f(m) - f(am). Thus colinearity is equivalent to E-linearity. The assignments
leave vector spaces and maps fixed, preserve identities and compositions, and their
composites recover both structures by step 7. This gives the categorical equivalence,
with the object assignments explicitly tied to the same structure bijections.
9. All sums allow empty bases. If M=0 both structures are unique. If E=0, then E^*=0,
the coalgebra maps are zero, and a unital action or counital coaction exists exactly
when M=0. Both structure sets are empty for nonzero M and singletons for zero M.
-/
theorem finite_algebra_comodule_duality [FiniteDimensional k E] :
    ∃ c : Coalgebra k (Module.Dual k E),
      IsDualCoalgebra c ∧
      (∀ c' : Coalgebra k (Module.Dual k E), IsDualCoalgebra c' → c' = c) ∧
      ∃ e : ∀ M : FGModuleCat.{w} k,
        (E →ₐ[k] Module.End k M) ≃ RightCoaction c M,
        (∀ (M : FGModuleCat.{w} k) (ρ : RightCoaction c M) (a : E) (m : M),
          (e M).symm ρ a m =
            TensorProduct.rid k M ((Module.Dual.eval k E a).lTensor M (ρ.val m))) ∧
        (∀ (M : FGModuleCat.{w} k) (α : E →ₐ[k] Module.End k M)
          (I : Type t) [Fintype I] (b : Module.Basis I k E) (m : M),
          (e M α).val m = ∑ i : I, α (b i) m ⊗ₜ[k] b.coord i) ∧
        (∀ (M N : FGModuleCat.{w} k)
          (α : E →ₐ[k] Module.End k M) (β : E →ₐ[k] Module.End k N)
          (f : M →ₗ[k] N),
          (∀ (a : E) (m : M), f (α a m) = β a (f m)) ↔
            (e N β).val ∘ₗ f = f.rTensor (Module.Dual k E) ∘ₗ (e M α).val) ∧
        ∃ Φ : LeftModule.{u, v, w} k E ≌ RightComodule.{u, v, w} c,
          Φ.functor ⋙ forgetRight c = forgetLeft ∧
          Φ.inverse ⋙ forgetLeft = forgetRight c ∧
          (∀ X : LeftModule.{u, v, w} k E,
            HEq (Φ.functor.obj X).coaction (e X.space X.action)) ∧
          (∀ Y : RightComodule.{u, v, w} c,
            HEq (Φ.inverse.obj Y).action ((e Y.space).symm Y.coaction)) := by
  sorry

end FiniteAlgebraComoduleDuality
