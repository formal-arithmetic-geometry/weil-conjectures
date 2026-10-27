module

public import Mathlib.RingTheory.TensorProduct.Maps

/-! # Evaluation from tensor-diagonal base change

Source: Stacks Project, Tag 0C2Y, second proof paragraph, displayed tensor identity,
generalized to commutative algebras over a commutative ring
(blueprint: lem-trf-tensor-diagonal-evaluation-hom).

## Main definitions and statements

- `Algebra.TensorProduct.tensorDiagonalBaseChange`: the source with its prescribed actions.
- `Algebra.TensorProduct.tensor_diagonal_evaluation_existsUnique`: unique evaluation ring map.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x

open scoped TensorProduct

namespace Algebra.TensorProduct

variable (k : Type u) (L : Type v) (B : Type w) (C : Type x)
variable [CommRing k] [CommRing L] [CommRing B] [CommRing C]
variable [Algebra k L] [Algebra L B] [Algebra L C]
variable [Algebra k B] [Algebra k C] [IsScalarTower k L B] [IsScalarTower k L C]

/-- The map ψ on the tensor square, sending `s ⊗ t` to their images in `B ⊗[k] C`.
Source: Stacks Project, Tag 0C2Y, second proof paragraph, displayed tensor identity
(blueprint: lem-trf-tensor-diagonal-evaluation-hom). -/
noncomputable def tensorDiagonalScalarMap : (L ⊗[k] L) →ₐ[k] B ⊗[k] C :=
  map (IsScalarTower.toAlgHom k L B) (IsScalarTower.toAlgHom k L C)

/-- The ring `(B ⊗[k] C) ⊗[L ⊗[k] L] L`, with the left action through ψ and the
right action through multiplication `L ⊗[k] L → L`. Both structures are constructed,
including in the zero-ring case.
Source: Stacks Project, Tag 0C2Y, second proof paragraph, displayed tensor identity
(blueprint: lem-trf-tensor-diagonal-evaluation-hom). -/
noncomputable def tensorDiagonalBaseChange : Type (max v w x) :=
  letI := (tensorDiagonalScalarMap k L B C).toRingHom.toAlgebra
  letI := (lmul' k (S := L)).toRingHom.toAlgebra
  (B ⊗[k] C) ⊗[L ⊗[k] L] L

/-- The ordinary tensor-product ring structure on the prescribed diagonal base change.
Source: Stacks Project, Tag 0C2Y, second proof paragraph, displayed tensor identity
(blueprint: lem-trf-tensor-diagonal-evaluation-hom). -/
noncomputable instance tensorDiagonalBaseChangeCommRing :
    CommRing (tensorDiagonalBaseChange k L B C) := by
  unfold tensorDiagonalBaseChange
  letI := (tensorDiagonalScalarMap k L B C).toRingHom.toAlgebra
  letI := (lmul' k (S := L)).toRingHom.toAlgebra
  infer_instance

/-- The double pure tensor `(b ⊗ c) ⊗ l` in the prescribed diagonal base change.
Source: Stacks Project, Tag 0C2Y, second proof paragraph, displayed tensor identity
(blueprint: lem-trf-tensor-diagonal-evaluation-hom). -/
noncomputable def tensorDiagonalPureTensor (b : B) (c : C) (l : L) :
    tensorDiagonalBaseChange k L B C :=
  letI := (tensorDiagonalScalarMap k L B C).toRingHom.toAlgebra
  letI := (lmul' k (S := L)).toRingHom.toAlgebra
  (b ⊗ₜ[k] c) ⊗ₜ[L ⊗[k] L] l

/-- There is a unique unital ring homomorphism from tensor-diagonal base change to
`B ⊗[L] C` sending `(b ⊗ c) ⊗ l` to `(l • b) ⊗ c`.
Source: Stacks Project, Tag 0C2Y, second proof paragraph, displayed tensor identity,
generalized to commutative algebras over a commutative ring
(blueprint: lem-trf-tensor-diagonal-evaluation-hom).

Proof:
1. The bilinear map `(b,c) ↦ b ⊗[L] c` is k-bilinear by restriction of scalars.
   The universal property of `def-weil-pbc-module-tensor-product` gives `q : D → H`.
2. L-balancing gives `q(ψ(s ⊗ t)(b ⊗ c)) = st • q(b ⊗ c)`.
   Pure tensors generate R and D, so biadditivity gives R-linearity of q for the
   prescribed actions, with R acting on H through multiplication R → L.
3. The map `(d,l) ↦ l • q(d)` is R-bilinear: q is R-linear, and scalars in L commute.
   The same tensor universal property gives β with the required pure-tensor formula.
4. β preserves the unit and products of double pure tensors by that formula.
   Applying pure-tensor generation twice expresses every element as a finite sum
   of double pure tensors; distributivity extends multiplicativity to all pairs.
   Empty sums include zero elements. Thus β is a unital ring homomorphism.
5. Any other unital ring homomorphism satisfying the formula agrees on every double
   pure tensor, and hence on every finite sum by additivity. This proves uniqueness
   among all unital ring homomorphisms without assuming R-linearity of competitors. -/
theorem tensor_diagonal_evaluation_existsUnique :
    ∃! β : tensorDiagonalBaseChange k L B C →+* B ⊗[L] C,
      ∀ (b : B) (c : C) (l : L),
        β (tensorDiagonalPureTensor k L B C b c l) = (l • b) ⊗ₜ[L] c := by
  sorry

end Algebra.TensorProduct
