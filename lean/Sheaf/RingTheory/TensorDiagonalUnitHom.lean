module

public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The unit map into the tensor-diagonal base change

Source: Stacks Project, Tag 0C2Y, second proof paragraph, displayed tensor identity;
its forward map generalized to arbitrary commutative algebras over a commutative ring
(blueprint: lem-trf-tensor-diagonal-unit-hom).

The auxiliary definitions fix the two scalar maps in the codomain, without installing
alternative algebra structures on the underlying rings as global instances.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open scoped TensorProduct

namespace Algebra.TensorProduct.Diagonal

section

variable (k : Type u) (L : Type v) (B : Type w) (C : Type z)
variable [CommRing k] [CommRing L] [CommRing B] [CommRing C]
variable [Algebra k L] [Algebra L B] [Algebra L C]
variable [Algebra k B] [Algebra k C] [IsScalarTower k L B] [IsScalarTower k L C]

/-- The map `ψ : L ⊗[k] L → B ⊗[k] C` taking `λ ⊗ λ'` to
`algebraMap L B λ ⊗ algebraMap L C λ'`.
Source: Stacks Project, Tag 0C2Y, displayed tensor identity, generalized forward map
(blueprint: lem-trf-tensor-diagonal-unit-hom). -/
noncomputable def scalarMap : L ⊗[k] L →ₐ[k] B ⊗[k] C :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom k L B) (IsScalarTower.toAlgHom k L C)

/-- The actual tensor product `(B ⊗[k] C) ⊗[L ⊗[k] L] L`, with the left scalar
map `scalarMap` and the right scalar map `λ ⊗ λ' ↦ λ * λ'`.
Source: Stacks Project, Tag 0C2Y, displayed tensor identity, generalized forward map
(blueprint: lem-trf-tensor-diagonal-unit-hom). -/
def baseChange : Type (max v w z) :=
  letI := (scalarMap k L B C).toRingHom.toAlgebra
  letI := (Algebra.TensorProduct.lmul' k (S := L)).toRingHom.toAlgebra
  (B ⊗[k] C) ⊗[L ⊗[k] L] L

/-- The standard commutative tensor ring structure on the diagonal base change.
Its multiplication multiplies the two tensor factors, and its unit is `1 ⊗ 1`.
Source: Stacks Project, Tags 0C2Y and 00CX
(blueprint: lem-trf-tensor-diagonal-unit-hom). -/
noncomputable instance baseChangeCommRing : CommRing (baseChange k L B C) :=
  letI := (scalarMap k L B C).toRingHom.toAlgebra
  letI := (Algebra.TensorProduct.lmul' k (S := L)).toRingHom.toAlgebra
  Algebra.TensorProduct.instCommRing

/-- A pure tensor `d ⊗ λ` in the diagonal base change with its prescribed scalar maps.
Source: Stacks Project, Tag 0C2Y, displayed tensor identity
(blueprint: lem-trf-tensor-diagonal-unit-hom). -/
noncomputable def baseChangeTmul (d : B ⊗[k] C) (a : L) : baseChange k L B C :=
  letI := (scalarMap k L B C).toRingHom.toAlgebra
  letI := (Algebra.TensorProduct.lmul' k (S := L)).toRingHom.toAlgebra
  d ⊗ₜ[L ⊗[k] L] a

end

/-- There is a unique unital ring map `B ⊗[L] C → (B ⊗[k] C) ⊗[L ⊗[k] L] L`
with `b ⊗ c ↦ (b ⊗ c) ⊗ 1`. The scalar tower instances express restriction of the
`L`-algebra structures to `k`; no nonzero or flatness assumption is needed.

Source: Stacks Project, Tag 0C2Y, second proof paragraph, generalized forward map
(blueprint: lem-trf-tensor-diagonal-unit-hom).

Proof plan:
1. The tensor-algebra pushout universal property
   (lem-weil-pbc-algebra-tensor-pushout-universal-property) supplies `ψ`, the
   multiplication map `μ`, the tensor ring structures and their unital inclusions.
   Write `Q = D ⊗[R] L`, `j(d) = d ⊗ 1`, `ℓ(λ) = 1 ⊗ λ`, and let
   `f(b) = j(b ⊗ 1)`, `g(c) = j(1 ⊗ c)`.
2. The balancing relations (def-weil-pbc-module-tensor-product) give
   `(ψ(r) * d) ⊗ a = d ⊗ (μ(r) * a)`. Taking `d = a = 1` and then
   `r = λ ⊗ 1` or `r = 1 ⊗ λ` gives
   `f(algebraMap L B λ) = ℓ(λ) = g(algebraMap L C λ)`.
   Thus `f` and `g` are maps of `L`-algebras.
3. Apply the tensor-algebra pushout property over `L`. The resulting map has
   value `f(b) * g(c) = (b ⊗ c) ⊗ 1` on every pure tensor.
4. Any competing ring map has the same restrictions to `B` and `C`. Its prescribed
   value on `(algebraMap L B λ) ⊗ 1`, together with step 2, makes it an `L`-algebra
   map. The uniqueness clause of the same pushout property therefore identifies it
   with the constructed map. All constructions allow zero rings. -/
theorem existsUnique_unitHom
    (k : Type u) (L : Type v) (B : Type w) (C : Type z)
    [CommRing k] [CommRing L] [CommRing B] [CommRing C]
    [Algebra k L] [Algebra L B] [Algebra L C]
    [Algebra k B] [Algebra k C] [IsScalarTower k L B] [IsScalarTower k L C] :
    ∃! α : B ⊗[L] C →+* baseChange k L B C,
      ∀ (b : B) (c : C), α (b ⊗ₜ[L] c) = baseChangeTmul k L B C (b ⊗ₜ[k] c) 1 := by
  sorry

end Algebra.TensorProduct.Diagonal
