/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Field.Basic

/-!
# Extension of scalars along an algebra map as a tensor product

For an `R`-algebra `S`, the object `(ModuleCat.extendScalars (algebraMap R S)).obj N` is the
tensor product `S ⊗[R] N` for the `R`-module structure on `S` coming from the algebra structure
(`ModuleCat.tensorEquivExtendScalars`). The two are not definitionally equal, since
`ModuleCat.extendScalars` uses the module structure on `S` obtained by restriction of scalars.
-/

@[expose] public section

universe u

open CategoryTheory TensorProduct

/-- For an `R`-algebra `S`, `S ⊗[R] N` is `(ModuleCat.extendScalars (algebraMap R S)).obj N`. -/
noncomputable def ModuleCat.tensorEquivExtendScalars (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{u} R) :
    S ⊗[R] N ≃ₗ[S] (ModuleCat.extendScalars (algebraMap R S)).obj N := by
  let T := (ModuleCat.extendScalars (algebraMap R S)).obj N
  let S' := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  let toFun : S ⊗[R] N →ₗ[R] TensorProduct R S' N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S' N s
        map_add' s s' := (TensorProduct.mk R S' N).map_add s s'
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S' N) (Algebra.smul_def r s)).trans
            ((TensorProduct.mk R S' N).map_smul r (s : S')) }
  let invFun : TensorProduct R S' N →ₗ[R] S ⊗[R] N :=
    TensorProduct.lift
      { toFun s := TensorProduct.mk R S N (show S from s)
        map_add' s s' := (TensorProduct.mk R S N).map_add (show S from s) (show S from s')
        map_smul' r s :=
          (congrArg (TensorProduct.mk R S N) (Algebra.smul_def r (show S from s)).symm).trans
            ((TensorProduct.mk R S N).map_smul r (show S from s)) }
  have h₁ : ∀ x, invFun (toFun x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h₂ : ∀ x, toFun (invFun x) = x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s n => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  exact
    { toFun := toFun
      invFun := invFun
      map_add' := toFun.map_add
      map_smul' s x := by
        induction x using TensorProduct.induction_on with
        | zero => exact (map_zero toFun).trans (show (0 : T) = s • (0 : T) from (smul_zero s).symm)
        | tmul s' n => rfl
        | add x y hx hy =>
          rw [smul_add, map_add, hx, hy, map_add]
          exact (smul_add s _ _).symm
      left_inv := h₁
      right_inv := h₂ }

lemma ModuleCat.tensorEquivExtendScalars_tmul (R S : Type u) [CommRing R] [CommRing S]
    [Algebra R S] (N : ModuleCat.{u} R) (s : S) (n : N) :
    ModuleCat.tensorEquivExtendScalars R S N (s ⊗ₜ n) =
      TensorProduct.tmul R
        (M := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S))
        s n :=
  rfl

/-- Let `A` be a `k`-algebra and `K/k` a field extension with a basis `bK`. For an `A`-module `N`,
the extension of scalars of `N` along `A ⟶ A ⊗[k] K` is the direct sum of copies of `N` indexed
by the basis, `(1 ⊗ bK b) ⊗ x` corresponding to `x` in the summand `b`. -/
lemma ModuleCat.exists_addEquiv_extendScalars_includeLeft {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] {K : Type u} [Field K] [Algebra k K] {ι : Type u} (bK : Module.Basis ι k K)
    (N : ModuleCat.{u} A) :
    ∃ E : (ModuleCat.extendScalars (Algebra.TensorProduct.includeLeftRingHom :
          A →+* A ⊗[k] K)).obj N ≃+ (ι →₀ N), ∀ (b : ι) (x : N),
      E (((1 : A) ⊗ₜ[k] bK b : A ⊗[k] K) ⊗ₜ[A] x) = Finsupp.single b x := by
  classical
  let f : A →+* A ⊗[k] K := Algebra.TensorProduct.includeLeftRingHom
  let P := (ModuleCat.restrictScalars f).obj (ModuleCat.of (A ⊗[k] K) (A ⊗[k] K))
  let e : (A ⊗[k] K) ≃ₗ[A] P :=
    { toFun := fun x ↦ (x : A ⊗[k] K)
      invFun := fun x ↦ (x : A ⊗[k] K)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun a x ↦ by
        change a • x = f a * x
        rw [Algebra.smul_def]
        rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let 𝒞 : Module.Basis ι A P := (Algebra.TensorProduct.basis A bK).map e
  refine ⟨(TensorProduct.equivFinsuppOfBasisLeft (N := N) 𝒞).toAddEquiv, fun b x ↦ ?_⟩
  have h𝒞 : 𝒞 b = e ((1 : A) ⊗ₜ[k] bK b) := by
    simp only [𝒞, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  change TensorProduct.equivFinsuppOfBasisLeft 𝒞 (e ((1 : A) ⊗ₜ[k] bK b) ⊗ₜ x) = _
  rw [← h𝒞, TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, Module.Basis.repr_self,
    Finsupp.mapRange_single, one_smul]
