/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.Tactic.LinearCombination

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Dual numbers: scaling, derivations and matrices

The `R`-algebra endomorphism `ε ↦ cε` of the dual numbers `R[ε]`, which is multiplicative in `c`
and reduces to the identity modulo `ε`; the derivation `D` of a `K`-algebra `A` attached to a
section `a ↦ a + D(a) ε` of the reduction `A[ε] → A`; and the arithmetic of matrices over `R[ε]`
whose reduction modulo `ε` is the identity: their `ε`-parts add under multiplication.
-/

@[expose] public section

open TrivSqZeroExt

namespace DualNumber

variable {R : Type*} [CommSemiring R]

section LiftElem

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- The `R`-algebra homomorphism `R[ε] → A`, `ε ↦ m`, for an element `m` of square zero. -/
def liftElem (m : A) (hm : m * m = 0) : R[ε] →ₐ[R] A :=
  lift ⟨(Algebra.ofId R A, m), hm, fun _ ↦ Commute.all _ _⟩

theorem liftElem_apply (m : A) (hm : m * m = 0) (x : R[ε]) :
    liftElem m hm x = algebraMap R A x.fst + algebraMap R A x.snd * m :=
  rfl

end LiftElem

/-- The `R`-algebra endomorphism `ε ↦ cε` of the dual numbers. -/
def scale (c : R) : R[ε] →ₐ[R] R[ε] :=
  TrivSqZeroExt.map (c • LinearMap.id)

@[simp]
theorem scale_inr (c x : R) : scale c (inr x) = inr (c * x) :=
  TrivSqZeroExt.map_inr _ _

@[simp]
theorem fst_scale (c : R) (x : R[ε]) : (scale c x).fst = x.fst :=
  TrivSqZeroExt.fst_map _ _

@[simp]
theorem snd_scale (c : R) (x : R[ε]) : (scale c x).snd = c * x.snd :=
  TrivSqZeroExt.snd_map _ _

@[simp]
theorem scale_one : scale (1 : R) = AlgHom.id R R[ε] := by
  ext <;> simp


section Derivation

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

/-- A section `ψ : A → A[ε]` of the reduction modulo `ε`, `ψ a = a + D(a) ε`, defines the
derivation `D` of `A`. -/
def derivationOfSection (ψ : A →ₐ[K] A[ε]) (hψ : (fstHom K A A).comp ψ = AlgHom.id K A) :
    Derivation K A A :=
  Derivation.mk'
    { toFun a := (ψ a).snd
      map_add' a b := by rw [map_add, snd_add]
      map_smul' c a := by rw [map_smul, snd_smul, RingHom.id_apply] }
    fun a b ↦ by
      have h (a : A) : (ψ a).fst = a := congr($hψ a)
      simp only [LinearMap.coe_mk, AddHom.coe_mk, map_mul, snd_mul, h, smul_eq_mul]
      ring

theorem derivationOfSection_apply (ψ : A →ₐ[K] A[ε])
    (hψ : (fstHom K A A).comp ψ = AlgHom.id K A) (a : A) :
    derivationOfSection ψ hψ a = (ψ a).snd :=
  rfl

/-- The `K`-algebra map `A[ε] → K[ε]`, `a + bε ↦ e(a) + e(b)ε`, induced by a `K`-point `e` of
`A`. -/
def mapOfAlgHom (e : A →ₐ[K] K) : A[ε] →ₐ[K] K[ε] :=
  lift ⟨((Algebra.ofId K K[ε]).comp e, ε), eps_mul_eps, fun _ ↦ Commute.all _ _⟩

@[simp]
theorem fst_mapOfAlgHom (e : A →ₐ[K] K) (x : A[ε]) : (mapOfAlgHom e x).fst = e x.fst := by
  simp [mapOfAlgHom, lift_apply_apply, Algebra.ofId_apply, algebraMap_eq_inl']

@[simp]
theorem snd_mapOfAlgHom (e : A →ₐ[K] K) (x : A[ε]) : (mapOfAlgHom e x).snd = e x.snd := by
  simp [mapOfAlgHom, lift_apply_apply, Algebra.ofId_apply, algebraMap_eq_inl']

variable (A) in
/-- The `K`-algebra map `K[ε] → A[ε]` induced by the structure map `K → A`. -/
def mapAlgebraMap : K[ε] →ₐ[K] A[ε] :=
  lift ⟨(Algebra.ofId K A[ε], ε), eps_mul_eps, fun _ ↦ Commute.all _ _⟩

@[simp]
theorem fst_mapAlgebraMap (x : K[ε]) : (mapAlgebraMap A x).fst = algebraMap K A x.fst := by
  simp [mapAlgebraMap, lift_apply_apply, Algebra.ofId_apply, algebraMap_eq_inl']

@[simp]
theorem snd_mapAlgebraMap (x : K[ε]) : (mapAlgebraMap A x).snd = algebraMap K A x.snd := by
  simp [mapAlgebraMap, lift_apply_apply, Algebra.ofId_apply, algebraMap_eq_inl']

theorem mul_self_eq_zero_of_fst_eq_zero {x : A[ε]} (hx : x.fst = 0) : x * x = 0 := by
  ext <;> simp [hx]

end Derivation

end DualNumber

namespace Matrix

variable {n : Type*} {R : Type*}

theorem map_inr_mul_map_inr [Fintype n] [Semiring R] (X Y : Matrix n n R) :
    X.map (inr : R → DualNumber R) * Y.map inr = 0 := by
  ext i j : 1
  simp only [Matrix.mul_apply, Matrix.map_apply, inr_mul_inr, Finset.sum_const_zero,
    Matrix.zero_apply]

variable [DecidableEq n] [CommRing R]

/-- A matrix over `R[ε]` reducing to the identity modulo `ε` is `1 + εX`, with `X` its `ε`-part. -/
theorem eq_one_add_map_inr_of_map_fst_eq_one {A : Matrix n n (DualNumber R)}
    (hA : A.map fst = 1) : A = 1 + (A.map snd).map inr := by
  ext i j : 1
  refine TrivSqZeroExt.ext ?_ ?_
  · simpa [Matrix.one_apply, apply_ite fst] using congr_fun₂ hA i j
  · simp [Matrix.one_apply, apply_ite snd]

variable [Fintype n] in
/-- For matrices over `R[ε]` reducing to the identity modulo `ε`, the `ε`-part of a product is
the sum of the `ε`-parts. -/
theorem map_snd_mul_of_map_fst_eq_one {A B : Matrix n n (DualNumber R)}
    (hA : A.map fst = 1) (hB : B.map fst = 1) :
    (A * B).map snd = A.map snd + B.map snd := by
  ext i j
  have hA' (i j) : (A i j).fst = (1 : Matrix n n R) i j := congr_fun₂ hA i j
  have hB' (i j) : (B i j).fst = (1 : Matrix n n R) i j := congr_fun₂ hB i j
  simp [Matrix.mul_apply, TrivSqZeroExt.snd_sum, hA', hB',
    Matrix.one_apply, Finset.sum_add_distrib, add_comm]

end Matrix

namespace DualNumber

/-! ### The units of the dual numbers -/

section Units

variable {R : Type*} [CommRing R]

/-- The unit `1 + εg` of `R[ε]`, as a homomorphism from the additive group of `R` to the
additively written group of units: `(1 + εa)(1 + εb) = 1 + ε(a + b)`. -/
def oneAddEps : R →+ Additive R[ε]ˣ where
  toFun g := Additive.ofMul ⟨1 + inr g, 1 - inr g, by
    rw [add_mul, one_mul, mul_sub, mul_one, inr_mul_inr, sub_zero, sub_add_cancel], by
    rw [sub_mul, one_mul, mul_add, mul_one, inr_mul_inr, add_zero, add_sub_cancel_right]⟩
  map_zero' := by
    refine Additive.toMul.injective (Units.ext ?_)
    simp
  map_add' a b := by
    refine congrArg Additive.ofMul (Units.ext ?_)
    change 1 + inr (a + b) = (1 + inr a) * (1 + inr b)
    rw [add_mul, one_mul, mul_add, mul_one, inr_mul_inr, add_zero, inr_add]
    abel

@[simp]
theorem val_oneAddEps (g : R) : ((Additive.toMul (oneAddEps g) : R[ε]ˣ) : R[ε]) = 1 + inr g :=
  rfl

end Units

end DualNumber
