/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Maps
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Tensor products of quotient algebras

## Main results

- `Algebra.TensorProduct.liftQuotient`: the homomorphism `(A ⧸ I) ⊗[R] (B ⧸ J) → C` induced by
  two homomorphisms killing `I` and `J`.
- `Algebra.TensorProduct.map_mkQ_restrictScalars_eq_zero_iff`: the module and algebra quotient
  maps by two ideals kill the same elements of `A ⊗[R] B`.
- `Algebra.TensorProduct.eq_zero_of_forall_lift_eq_zero`,
  `Algebra.TensorProduct.eq_zero_of_forall_liftQuotient_eq_zero`: over a field, an element of a
  tensor product of algebras is detected on pairs of characters from jointly injective families.
  For quotients by the ideals of common zeros of two families of `K`-points this says that the
  product of the two families is schematically dense in the product of their Zariski closures.
-/

@[expose] public section

open scoped TensorProduct

namespace Algebra.TensorProduct

section CommRing

variable {R A B C : Type*} [CommRing R] [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
  [CommRing C] [Algebra R C] (I : Ideal A) (J : Ideal B)

/-- The algebra homomorphism `(A ⧸ I) ⊗[R] (B ⧸ J) → C` induced by two algebra homomorphisms
`f : A → C` and `g : B → C` killing `I` and `J`. -/
noncomputable def liftQuotient (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hf : ∀ a ∈ I, f a = 0)
    (hg : ∀ b ∈ J, g b = 0) : (A ⧸ I) ⊗[R] (B ⧸ J) →ₐ[R] C :=
  lift (Ideal.Quotient.liftₐ I f hf) (Ideal.Quotient.liftₐ J g hg) fun _ _ ↦ .all _ _

variable {I J}

@[simp]
theorem liftQuotient_tmul (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hf : ∀ a ∈ I, f a = 0)
    (hg : ∀ b ∈ J, g b = 0) (a : A) (b : B) :
    liftQuotient I J f g hf hg (Ideal.Quotient.mk I a ⊗ₜ Ideal.Quotient.mk J b) = f a * g b :=
  rfl

theorem liftQuotient_map_mkₐ (f : A →ₐ[R] C) (g : B →ₐ[R] C) (hf : ∀ a ∈ I, f a = 0)
    (hg : ∀ b ∈ J, g b = 0) (t : A ⊗[R] B) :
    liftQuotient I J f g hf hg (map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J) t) =
      lift f g (fun _ _ ↦ .all _ _) t := by
  induction t using _root_.TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [liftQuotient]
  | add a b ha hb => simp only [map_add, ha, hb]

variable (I J) in
/-- The tensor product of the module quotient maps by the ideals `I` and `J`, viewed as
`R`-submodules, kills an element if and only if the tensor product of the algebra quotient maps
does. -/
theorem map_mkQ_restrictScalars_eq_zero_iff (t : A ⊗[R] B) :
    _root_.TensorProduct.map (I.restrictScalars R).mkQ (J.restrictScalars R).mkQ t = 0 ↔
      map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J) t = 0 := by
  let e := _root_.TensorProduct.congr (Submodule.Quotient.restrictScalarsEquiv R I)
    (Submodule.Quotient.restrictScalarsEquiv R J)
  have key (t : A ⊗[R] B) : e (_root_.TensorProduct.map (I.restrictScalars R).mkQ
      (J.restrictScalars R).mkQ t) = map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R J) t := by
    induction t using _root_.TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [e]
    | add a b ha hb => simp only [map_add, ha, hb]
  rw [← key, LinearEquiv.map_eq_zero_iff]

end CommRing

section Field

variable {K A B : Type*} [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]

/-- Over a field `K`, an element of `A ⊗[K] B` vanishes as soon as it is killed by every
`lift (f i) (g j)`, for jointly injective families of characters `f i : A → K` and `g j : B → K`.

The images of `x` in `K ⊗[K] B = B` under the `f i ⊗ B` are killed by every `g j`, so they vanish,
and `TensorProduct.eq_zero_of_forall_rTensor_eq_zero` applies. -/
theorem eq_zero_of_forall_lift_eq_zero {ι κ : Type*} (f : ι → A →ₐ[K] K) (g : κ → B →ₐ[K] K)
    (hf : ∀ a, (∀ i, f i a = 0) → a = 0) (hg : ∀ b, (∀ j, g j b = 0) → b = 0)
    {x : A ⊗[K] B} (hx : ∀ i j, lift (f i) (g j) (fun _ _ ↦ .all _ _) x = 0) : x = 0 := by
  refine _root_.TensorProduct.eq_zero_of_forall_rTensor_eq_zero (fun i ↦ (f i).toLinearMap) hf
    fun i ↦ ?_
  have key (j : κ) (y : A ⊗[K] B) :
      g j (_root_.TensorProduct.lid K B ((f i).toLinearMap.rTensor B y)) =
        lift (f i) (g j) (fun _ _ ↦ .all _ _) y := by
    induction y using _root_.TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add a b ha hb => simp only [map_add, ha, hb]
  refine (_root_.TensorProduct.lid K B).injective ?_
  rw [map_zero]
  exact hg _ fun j ↦ (key j x).trans (hx i j)

/-- Let `I ⊆ A` and `J ⊆ B` be the ideals of common zeros of two families of `K`-points `χ s` and
`χ' t`. An element of `(A ⧸ I) ⊗[K] (B ⧸ J)` vanishing at every pair of points `(χ s, χ' t)` is
zero: the product of the two families is schematically dense in the product of their Zariski
closures. -/
theorem eq_zero_of_forall_liftQuotient_eq_zero {I : Ideal A} {J : Ideal B} {S T : Type*}
    (χ : S → A →ₐ[K] K) (χ' : T → B →ₐ[K] K) (hI : ∀ a, a ∈ I ↔ ∀ s, χ s a = 0)
    (hJ : ∀ b, b ∈ J ↔ ∀ t, χ' t b = 0) {c : (A ⧸ I) ⊗[K] (B ⧸ J)}
    (hc : ∀ s t, liftQuotient I J (χ s) (χ' t) (fun a ha ↦ (hI a).1 ha s)
      (fun b hb ↦ (hJ b).1 hb t) c = 0) : c = 0 := by
  refine eq_zero_of_forall_lift_eq_zero
    (fun s ↦ Ideal.Quotient.liftₐ I (χ s) fun a ha ↦ (hI a).1 ha s)
    (fun t ↦ Ideal.Quotient.liftₐ J (χ' t) fun b hb ↦ (hJ b).1 hb t) (fun v hv ↦ ?_)
    (fun v hv ↦ ?_) hc
  · induction v using Quotient.inductionOn' with | h a => ?_
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hI a).2 hv)
  · induction v using Quotient.inductionOn' with | h b => ?_
    exact Ideal.Quotient.eq_zero_iff_mem.2 ((hJ b).2 hv)

end Field

end Algebra.TensorProduct
