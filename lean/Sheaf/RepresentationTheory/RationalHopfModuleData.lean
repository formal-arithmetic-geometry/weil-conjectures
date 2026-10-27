module

public import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.FiniteType

/-! # Rational Hopf modules over a commutative ring

Source: Alper, Adequate moduli spaces, Lemma 9.2.5 and Remark 9.2.7;
Stacks, groupoids, Tag 03LF, affine coactions.
(blueprint: def-sfb-rational-hopf-module-data)
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct Pointwise

namespace RationalHopfModule

variable (A : Type u) [CommRing A] (C : Type v) [CommRing C] [HopfAlgebra A C]
variable (M : Type w) [AddCommGroup M] [Module A M]

/-- A rational module in right-coordinate-coaction convention, without finiteness assumptions.
Source: Stacks Tag 03LF, affine translation.
(blueprint: def-sfb-rational-hopf-module-data) -/
structure Coaction where
  /-- The underlying linear coaction. -/
  map : M →ₗ[A] M ⊗[A] C
  /-- The counit identity. -/
  counit : (TensorProduct.rid A M).toLinearMap ∘ₗ
    (Coalgebra.counit (R := A) (A := C)).lTensor M ∘ₗ map = LinearMap.id
  /-- The coassociativity identity. -/
  coassoc : (TensorProduct.assoc A M C C).toLinearMap ∘ₗ map.rTensor C ∘ₗ map =
    (Coalgebra.comul (R := A) (A := C)).lTensor M ∘ₗ map

/-- The degree-n component, as the span of products of n linear generators.
Source: Stacks, Algebra, Section 00DM; SymmetricAlgebra.graded_by_tensor_images.
(blueprint: def-sfb-rational-hopf-module-data) -/
def degree (n : ℕ) : Submodule A (SymmetricAlgebra A M) :=
  (SymmetricAlgebra.ι A M).range ^ n

/-- The induced symmetric-algebra coaction, defined by its values on generators.
Source: Alper, Lemma 9.2.5; Stacks Tag 03LF.
(blueprint: def-sfb-rational-hopf-module-data) -/
def symmetricMap (ρ : M →ₗ[A] M ⊗[A] C) :
    SymmetricAlgebra A M →ₐ[A] SymmetricAlgebra A M ⊗[A] C :=
  SymmetricAlgebra.lift
    (TensorProduct.map (SymmetricAlgebra.ι A M) (LinearMap.id : C →ₗ[A] C) ∘ₗ ρ)

/-- The contragredient coaction in a finite free basis: its matrix is the antipode transpose.
Source: Alper, Remark 9.2.7, dualization; the basis formula is the usual contragredient.
The chosen Mathlib finite basis only computes this canonical map.
(blueprint: def-sfb-rational-hopf-module-data) -/
noncomputable def dualMap [Nontrivial A] [Module.Free A M] [Module.Finite A M]
    (ρ : Coaction A C M) : Module.Dual A M →ₗ[A] Module.Dual A M ⊗[A] C :=
  (Module.finBasis A M).dualBasis.constr A (fun i ↦
    ∑ j, (Module.finBasis A M).coord j ⊗ₜ[A]
      HopfAlgebra.antipode A
        ((TensorProduct.lid A C)
          (((Module.finBasis A M).coord i).rTensor C (ρ.map (Module.finBasis A M j)))))

end RationalHopfModule
