module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import WeilConjectures.LinearAlgebra.SymmetricAlgebra.Graded

/-! # Invariant symmetric-power lifting over a ring

Source: Alper, Adequate moduli spaces and geometrically reductive group schemes,
Lemma 9.2.5(5), printed p.522.
(blueprint: def-sfb-invariant-symmetric-power-lifting)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace AlgebraicGeometry.InvariantSymmetricPower

variable (R : Type u) [CommRing R] (C : Type w) [CommRing C] [HopfAlgebra R C]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The right-comodule identities for a rational module, without finiteness assumptions.
Source: Alper, Lemma 9.2.5, p.522, rational G-R-modules.
(blueprint: def-sfb-invariant-symmetric-power-lifting) -/
def IsCoaction (ρ : M →ₗ[R] M ⊗[R] C) : Prop :=
  (TensorProduct.rid R M).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := C)).lTensor M ∘ₗ ρ = LinearMap.id ∧
    (TensorProduct.assoc R M C C).toLinearMap ∘ₗ ρ.rTensor C ∘ₗ ρ =
      (Coalgebra.comul (R := R) (A := C)).lTensor M ∘ₗ ρ

/-- The induced algebra coaction is the unique algebra map extending the module coaction.
Its restriction to each homogeneous component is the symmetric-power coaction.
Source: Alper, Lemma 9.2.5(4),(5), p.522.
(blueprint: def-sfb-invariant-symmetric-power-lifting) -/
def symmetricCoaction (ρ : M →ₗ[R] M ⊗[R] C) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R M ⊗[R] C :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).rTensor C ∘ₗ ρ)

/-- P(R,C): every equivariant surjection onto the trivial module admits a positive-degree
homogeneous invariant lifting of 1. Evaluation by `lift lam` is Sym^n(lam) followed by the
canonical Sym^n(R) = R identification. The component is the tensor image used in the
recorded symmetric-algebra grading, so arbitrary torsion modules are included.
Source: Alper, Lemma 9.2.5(5), p.522.
(blueprint: def-sfb-invariant-symmetric-power-lifting) -/
def HasInvariantPowerLifting : Prop :=
  ∀ (N : Type (max u v)) [AddCommGroup N] [Module R N]
    (ρ : N →ₗ[R] N ⊗[R] C), IsCoaction R C N ρ →
    ∀ (lam : N →ₗ[R] R), Function.Surjective lam →
      (∀ m : N, lam.rTensor C (ρ m) = lam m ⊗ₜ[R] (1 : C)) →
      ∃ (n : ℕ) (_ : 0 < n) (q : SymmetricAlgebra R N),
        q ∈ (((TensorAlgebra.ι R : N →ₗ[R] TensorAlgebra R N).range ^ n).map
          (SymmetricAlgebra.algHom R N).toLinearMap) ∧
        symmetricCoaction R C N ρ q = q ⊗ₜ[R] (1 : C) ∧
        SymmetricAlgebra.lift lam q = 1

end AlgebraicGeometry.InvariantSymmetricPower
