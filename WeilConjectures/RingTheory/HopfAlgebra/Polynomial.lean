/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.RingTheory.Bialgebra.Convolution
public import WeilConjectures.RingTheory.HopfAlgebra.HopfIdeal

/-!
# The Hopf algebra of the additive group

The polynomial ring `k[X]` over a commutative ring `k` is a commutative Hopf algebra, the
coordinate ring of the additive group `𝔾ₐ`: the variable `X` is primitive,
`Δ(X) = X ⊗ 1 + 1 ⊗ X`, with counit `ε(X) = 0` and antipode `S(X) = -X`. A `k`-algebra
homomorphism `k[X] → R` is the same as an element of `R`, and the convolution product of algebra
homomorphisms corresponds to addition (`Polynomial.algHomMulEquiv`).

When `k` is a field of characteristic `p > 0` the ideal `(X ^ p)` is a Hopf ideal, because
`(X ⊗ 1 + 1 ⊗ X) ^ p = X ^ p ⊗ 1 + 1 ⊗ X ^ p` in characteristic `p`; it cuts out the Frobenius
kernel `α_p` of `𝔾ₐ`.

## Main definitions

- `Polynomial.instBialgebra`, `Polynomial.instHopfAlgebra`: the Hopf algebra structure on `k[X]`
  in which `X` is primitive.
- `Polynomial.algHomMulEquiv`: `k`-algebra homomorphisms `k[X] → R`, with the convolution product,
  are the additive group of `R`.
- `Polynomial.frobeniusKernelIdeal`: the Hopf ideal `(X ^ p)` of the Frobenius kernel `α_p`.
-/

@[expose] public section

open TensorProduct

namespace Polynomial

variable (k : Type*) [CommRing k]

/-- The comultiplication `X ↦ X ⊗ 1 + 1 ⊗ X` of the coordinate ring of the additive group. -/
noncomputable def addComulAlgHom : k[X] →ₐ[k] k[X] ⊗[k] k[X] :=
  aeval (X ⊗ₜ 1 + 1 ⊗ₜ X)

/-- The counit `X ↦ 0` of the coordinate ring of the additive group: evaluation at `0`. -/
noncomputable def addCounitAlgHom : k[X] →ₐ[k] k :=
  aeval 0

/-- The antipode `X ↦ -X` of the coordinate ring of the additive group. -/
noncomputable def negAlgHom : k[X] →ₐ[k] k[X] :=
  aeval (-X)

@[simp]
theorem addComulAlgHom_X : addComulAlgHom k X = X ⊗ₜ 1 + 1 ⊗ₜ X :=
  aeval_X _

@[simp]
theorem addCounitAlgHom_X : addCounitAlgHom k X = 0 :=
  aeval_X _

@[simp]
theorem negAlgHom_X : negAlgHom k X = -X :=
  aeval_X _

theorem addComulAlgHom_coassoc :
    (Algebra.TensorProduct.assoc k k k k[X] k[X] k[X]).toAlgHom.comp
        ((Algebra.TensorProduct.map (addComulAlgHom k) (.id k _)).comp (addComulAlgHom k)) =
      (Algebra.TensorProduct.map (.id k _) (addComulAlgHom k)).comp (addComulAlgHom k) := by
  refine algHom_ext ?_
  simp only [AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply, addComulAlgHom_X,
    map_add, Algebra.TensorProduct.map_tmul, map_one, AlgHom.coe_id, id_eq, add_tmul, tmul_add,
    Algebra.TensorProduct.assoc_tmul, Algebra.TensorProduct.one_def]
  abel

theorem map_addCounitAlgHom_id_comp_addComulAlgHom :
    (Algebra.TensorProduct.map (addCounitAlgHom k) (.id k _)).comp (addComulAlgHom k) =
      (Algebra.TensorProduct.lid k k[X]).symm := by
  refine algHom_ext ?_
  simp

theorem map_id_addCounitAlgHom_comp_addComulAlgHom :
    (Algebra.TensorProduct.map (.id k _) (addCounitAlgHom k)).comp (addComulAlgHom k) =
      (Algebra.TensorProduct.rid k k k[X]).symm := by
  refine algHom_ext ?_
  simp

/-- The polynomial ring `k[X]` is a bialgebra in which `X` is primitive: the coordinate ring of
the additive group `𝔾ₐ`. -/
noncomputable instance instBialgebra : Bialgebra k k[X] :=
  Bialgebra.ofAlgHom (addComulAlgHom k) (addCounitAlgHom k) (addComulAlgHom_coassoc k)
    (map_addCounitAlgHom_id_comp_addComulAlgHom k) (map_id_addCounitAlgHom_comp_addComulAlgHom k)

@[simp]
theorem comul_X : Coalgebra.comul (R := k) (X : k[X]) = X ⊗ₜ 1 + 1 ⊗ₜ X :=
  addComulAlgHom_X k

@[simp]
theorem counit_X : Coalgebra.counit (R := k) (X : k[X]) = 0 :=
  addCounitAlgHom_X k

theorem lift_negAlgHom_comp_comulAlgHom :
    (Algebra.TensorProduct.lift (negAlgHom k) (.id k _) fun _ _ ↦ Commute.all _ _).comp
      (Bialgebra.comulAlgHom k k[X]) = (Algebra.ofId k _).comp (Bialgebra.counitAlgHom k k[X]) := by
  refine algHom_ext ?_
  simp

theorem lift_negAlgHom_comp_comulAlgHom' :
    (Algebra.TensorProduct.lift (.id k _) (negAlgHom k) fun _ _ ↦ Commute.all _ _).comp
      (Bialgebra.comulAlgHom k k[X]) = (Algebra.ofId k _).comp (Bialgebra.counitAlgHom k k[X]) := by
  refine algHom_ext ?_
  simp

/-- The polynomial ring `k[X]` is a commutative Hopf algebra, with antipode `X ↦ -X`: the
coordinate ring of the additive group `𝔾ₐ`. -/
noncomputable instance instHopfAlgebra : HopfAlgebra k k[X] :=
  HopfAlgebra.ofAlgHom (negAlgHom k) (lift_negAlgHom_comp_comulAlgHom k)
    (lift_negAlgHom_comp_comulAlgHom' k)

@[simp]
theorem antipode_X : HopfAlgebra.antipode k (X : k[X]) = -X :=
  negAlgHom_X k

instance instIsCocomm : Coalgebra.IsCocomm k k[X] where
  comm_comp_comul := by
    have h : (Algebra.TensorProduct.comm k k[X] k[X]).toAlgHom.comp (addComulAlgHom k) =
        addComulAlgHom k := by
      refine algHom_ext ?_
      simp [add_comm]
    exact congr(($h).toLinearMap)

variable {k} (R : Type*) [CommRing R] [Algebra k R]

/-- `k`-algebra homomorphisms `k[X] → R`, with the convolution product, are the additive group of
`R`: a homomorphism corresponds to its value at `X`. -/
noncomputable def algHomMulEquiv : WithConv (k[X] →ₐ[k] R) ≃* Multiplicative R where
  toFun φ := Multiplicative.ofAdd (φ.ofConv X)
  invFun r := WithConv.toConv (aeval r.toAdd)
  left_inv φ := by
    refine WithConv.ext (algHom_ext ?_)
    simp
  right_inv r := by simp
  map_mul' φ ψ := by
    simp [AlgHom.convMul_apply, ← ofAdd_add]

variable {R}

@[simp]
theorem algHomMulEquiv_apply (φ : WithConv (k[X] →ₐ[k] R)) :
    algHomMulEquiv R φ = Multiplicative.ofAdd (φ.ofConv X) :=
  rfl

end Polynomial

section FrobeniusKernel

/-- In an algebra over a field of characteristic `p`, the `p`-th power map is additive. -/
theorem add_pow_char_of_algebra (k : Type*) {B : Type*} [Field k] [CommRing B] [Algebra k B]
    (p : ℕ) [Fact p.Prime] [CharP k p] (x y : B) : (x + y) ^ p = x ^ p + y ^ p := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · exact Subsingleton.elim _ _
  · have := charP_of_injective_algebraMap (algebraMap k B).injective p
    exact add_pow_char x y p

namespace Polynomial

section Ideal

variable (k : Type*) [CommRing k] (p : ℕ)

/-- The ideal `(X ^ p)` of `k[X]`. For a field `k` of characteristic `p` it is a Hopf ideal,
cutting out the Frobenius kernel `α_p = Spec k[X] ⧸ (X ^ p)` of the additive group. -/
noncomputable def frobeniusKernelIdeal : Ideal k[X] :=
  Ideal.span {X ^ p}

theorem X_pow_mem_frobeniusKernelIdeal : (X : k[X]) ^ p ∈ frobeniusKernelIdeal k p :=
  Ideal.subset_span rfl

end Ideal

variable {k : Type*} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- The comultiplication of `X ^ p` in characteristic `p`: `X ^ p` is primitive. -/
theorem comul_X_pow_char :
    Coalgebra.comul (R := k) ((X : k[X]) ^ p) = (X ^ p) ⊗ₜ[k] 1 + 1 ⊗ₜ[k] (X ^ p) := by
  rw [← Bialgebra.comulAlgHom_apply, map_pow, Bialgebra.comulAlgHom_apply, comul_X,
    add_pow_char_of_algebra k, Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.tmul_pow]
  simp

/-- In characteristic `p` the ideal `(X ^ p)` is a Hopf ideal of `k[X]`. -/
instance isHopfIdeal_frobeniusKernelIdeal : (frobeniusKernelIdeal k p).IsHopfIdeal k := by
  refine Ideal.isHopfIdeal_span ?_ ?_ ?_ <;> rintro x rfl
  · rw [← Bialgebra.counitAlgHom_apply, map_pow, Bialgebra.counitAlgHom_apply, counit_X,
      zero_pow (Fact.out : p.Prime).ne_zero]
  · have h : Ideal.Quotient.mkₐ k (Ideal.span {(X : k[X]) ^ p}) (X ^ p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (X_pow_mem_frobeniusKernelIdeal k p)
    rw [comul_X_pow_char, map_add, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.map_tmul, h, zero_tmul, map_one, tmul_zero, add_zero]
  · rw [← HopfAlgebra.antipodeAlgHom_apply, map_pow, HopfAlgebra.antipodeAlgHom_apply,
      antipode_X, neg_pow]
    exact Ideal.mul_mem_left _ _ (X_pow_mem_frobeniusKernelIdeal k p)

end Polynomial

end FrobeniusKernel
