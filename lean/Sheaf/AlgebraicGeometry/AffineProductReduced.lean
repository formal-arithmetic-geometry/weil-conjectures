module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.Mathlib.RingTheory.Nullstellensatz
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Products of reduced affine varieties

Source: the Weil conjectures blueprint, `sec-algebraic-groups-lie-algebras`,
`sk-i-cartier/lem-wf-affine-product-reduced.md` and its proof
(blueprint: lem-wf-affine-product-reduced).

Affine varieties are represented by their reduced finitely generated coordinate algebras.
The cartesian square below identifies the spectrum of the tensor product with the product
over the base field. Rational points are algebra homomorphisms to the base field, and regular
maps to an affine variety are written contravariantly as maps of coordinate algebras.
-/

@[expose] public section

universe u v

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

/-- Products of reduced affine varieties over an algebraically closed field are reduced
affine varieties, their rational points are pairs, and functions and regular maps are
determined by evaluation at those pairs.

Source: the Weil conjectures blueprint, `sk-i-cartier/lem-wf-affine-product-reduced.md`
and its proof (blueprint: lem-wf-affine-product-reduced).

Proof: (1) The tensors of finite algebra generators of each factor generate the tensor
algebra, by the module tensor construction and the multiplication of pure tensors
(`def-weil-pbc-finite-type-algebra`, `def-weil-pbc-module-tensor-product`, and
`lem-weil-pbc-algebra-tensor-pushout-universal-property`).
(2) The affine fibre-product formula identifies the product with this spectrum. The tensor
universal property identifies its algebra maps to `k` with pairs of algebra maps from the
factors, with evaluation `a ⊗ b ↦ x(a)y(b)` (`lem-weil-pbc-fibre-product-affine-spectra`
and `def-weil-affine-spectrum`).
(3) Choose a basis of `B` (`lem-weil-pbc-vector-space-basis-through-vector`). Write a nonzero
tensor as a finite sum `∑ aᵢ ⊗ bᵢ` with the `bᵢ` linearly independent and some `aᵢ ≠ 0`.
(4) The vanishing principle for `A` gives a point `x` where that coefficient is nonzero.
Evaluation in the first factor gives the nonzero element `∑ x(aᵢ)bᵢ` of `B`. The vanishing
principle for `B` then gives a point `y` where this element is nonzero
(`lem-wf-affine-nullstellensatz-vanishing`). Tensor uniqueness identifies this iterated
evaluation with `Algebra.TensorProduct.productMap x y`.
(5) A nilpotent tensor evaluates to a nilpotent in the field `k`, hence to zero everywhere;
the preceding detection argument forces it to be zero. The same argument gives the
displayed vanishing principle, including when either coordinate algebra is zero.
(6) If two regular maps to `Spec C` agree at every pair, the difference of their pullbacks
of each element of `C` vanishes at every pair. Step (4) makes every such difference zero,
so the coordinate maps, and hence the regular maps, are equal by the affine-spectrum
correspondence (`def-weil-affine-spectrum`). The nested quantifiers express checking one
variable at a time. -/
theorem affine_product_reduced (k A B : Type u) [Field k] [IsAlgClosed k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra.FiniteType k A] [Algebra.FiniteType k B] [_root_.IsReduced A]
    [_root_.IsReduced B] :
    _root_.IsReduced (A ⊗[k] B) ∧
    Algebra.FiniteType k (A ⊗[k] B) ∧
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap k A)))
      (Spec.map (CommRingCat.ofHom (algebraMap k B))) ∧
    Function.Bijective
      (fun xy : (A →ₐ[k] k) × (B →ₐ[k] k) ↦
        Algebra.TensorProduct.productMap xy.1 xy.2) ∧
    (∀ t : A ⊗[k] B,
      (∀ (x : A →ₐ[k] k) (y : B →ₐ[k] k),
        Algebra.TensorProduct.productMap x y t = 0) → t = 0) ∧
    (∀ (C : Type v) [CommRing C] [Algebra k C] [Algebra.FiniteType k C]
      [_root_.IsReduced C] (f g : C →ₐ[k] A ⊗[k] B),
      (∀ (x : A →ₐ[k] k) (y : B →ₐ[k] k),
        (Algebra.TensorProduct.productMap x y).comp f =
          (Algebra.TensorProduct.productMap x y).comp g) → f = g) := by
  sorry

end AlgebraicGeometry
