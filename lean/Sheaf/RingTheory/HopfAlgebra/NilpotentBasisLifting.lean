module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.HopfAlgebra.Convolution
public import Mathlib.RingTheory.Bialgebra.Hom
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.RingHom.Flat

/-! # Lifting a basis over an infinitesimal Hopf subalgebra

Source: Milne, Algebraic Groups (2017), Theorem 3.31, printed pp. 73--74,
the nilpotent-augmentation case.
(blueprint: lem-sfb-nilpotent-hopf-basis-lifting)
-/

@[expose] public section

universe u v w z

namespace HopfAlgebra

/-- Any family lifting a basis modulo the extended augmentation ideal is a basis over
the Hopf subalgebra. The conclusion is bijectivity of the specified finite-support
sum, whose scalar action is `a • b = i a * b`; hence it says that the specified
`A`-linear map is an isomorphism. No finiteness condition is imposed on `J`.

Source: Milne, Algebraic Groups (2017), Theorem 3.31, printed pp. 73--74,
the nilpotent-augmentation case.
(blueprint: lem-sfb-nilpotent-hopf-basis-lifting)

Proof plan (using the repaired argument recorded in the DAG):
1. Choose finitely many algebra generators of A using def-weil-pbc-finite-type-algebra.
   Subtract their counits to obtain generators in I. Monomials of degree at least n
   vanish, so the finitely many monomials of degree less than n span A over k.
2. Apply lem-sfb-finite-hopf-self-injective to the inclusion A -> B and the identity
   of A, obtaining an A-linear retraction B -> A.
3. Hopf compatibility implies the right coideal condition. Apply
   lem-sfb-split-coideal-faithfully-flat to this retraction. Commutativity makes it
   a bimodule retraction. By def-weil-pbc-faithfully-flat-ring-map, B is flat over A.
4. Let F be the finite-support free module and q the asserted sum map. Its residue
   map is bijective by the basis hypothesis (def-weil-pbc-free-module). Its cokernel
   C satisfies C = IC, hence C = I^n C = 0. Thus q is onto and N = ker q lies in IF.
5. Tensor N -> F -> B -> 0 with I. By lem-weil-pbc-tensor-right-exact its kernel
   is the image of I tensor N. Multiplication I tensor B -> B is injective by
   flatness (def-weil-pbc-flat-ring-map), applied to I -> A. For x in N, choose
   u in I tensor F multiplying to x. Its image in I tensor B vanishes, so lift u
   from I tensor N. Multiplication (def-weil-pbc-module-tensor-product) then
   gives x in IN. Consequently N = IN.
6. Iterate N = IN to get N = I^n N = 0. The sum map is injective and surjective.
   Both nilpotence arguments apply to arbitrary, possibly infinite, J. -/
theorem bijective_lift_quotient_basis_of_nilpotent_augmentation
    (k : Type u) (A : Type v) (B : Type w)
    [Field k] [IsAlgClosed k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B]
    (hA : (algebraMap k A).FiniteType) (hB : (algebraMap k B).FiniteType)
    (i : A →ₐc[k] B) (hi : Function.Injective i)
    (hS : ∀ a : A, i (antipode k a) = antipode k (i a))
    (n : ℕ) (hn : 1 ≤ n) (hI : RingHom.ker (Bialgebra.counitAlgHom k A) ^ n = ⊥)
    (J : Type z) (e : J → B)
    (b : Module.Basis J k
      (B ⧸ (RingHom.ker (Bialgebra.counitAlgHom k A)).map i.toAlgHom.toRingHom))
    (he : ∀ j : J, b j = Ideal.Quotient.mkₐ k
      ((RingHom.ker (Bialgebra.counitAlgHom k A)).map i.toAlgHom.toRingHom) (e j)) :
    Function.Bijective (fun c : J →₀ A ↦ c.sum (fun j a ↦ i a * e j)) := by
  sorry

end HopfAlgebra
