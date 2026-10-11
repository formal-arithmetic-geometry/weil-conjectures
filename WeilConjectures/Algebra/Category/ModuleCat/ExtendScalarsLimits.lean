/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Extension of scalars along a finite projective ring map preserves limits

If `S` is finite projective as an `R`-module via `f : R →+* S`, then `S ⊗_R M ≅ Hom_R(S^∨, M)`
naturally in `M`, so `restrictScalars f ∘ extendScalars f` is a right adjoint, hence preserves
limits; since `restrictScalars f` preserves and reflects limits, so does `extendScalars f`
(`ModuleCat.preservesLimits_extendScalars`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ModuleCat

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  [Module.Finite R ((restrictScalars f).obj (of S S))]
  [Module.Projective R ((restrictScalars f).obj (of S S))]

/-- The `R`-linear identification `S ⊗_R M ≅ Hom_R(S^∨, M)` for `S` finite projective over `R`,
on the restriction of the extension of scalars. -/
noncomputable def extendScalarsDualEquiv (M : ModuleCat.{u} R) :
    (restrictScalars f).obj ((extendScalars f).obj M) ≃ₗ[R]
      (Module.Dual R ((restrictScalars f).obj (of S S)) →ₗ[R] M) :=
  let e := (TensorProduct.congr (Module.evalEquiv R ((restrictScalars f).obj (of S S)))
      (LinearEquiv.refl R M)).trans (dualTensorHomEquiv R _ M)
  { e.toAddEquiv with
    map_smul' r x := by
      change e _ = r • e x
      rw [← map_smul] }

lemma extendScalarsDualEquiv_tmul {M : ModuleCat.{u} R} (s : (restrictScalars f).obj (of S S))
    (m : M) (φ : Module.Dual R ((restrictScalars f).obj (of S S))) :
    extendScalarsDualEquiv f M (s ⊗ₜ[R] m) φ = φ s • m := by
  simp [extendScalarsDualEquiv, dualTensorHomEquiv]

/-- Extension of scalars followed by restriction is the internal Hom out of the dual `S^∨`. -/
noncomputable def extendScalarsCompRestrictScalarsIso :
    extendScalars.{u, u, u} f ⋙ restrictScalars.{u} f ≅
      ihom (of R (Module.Dual R ((restrictScalars f).obj (of S S)))) :=
  NatIso.ofComponents
    (fun M ↦ ((extendScalarsDualEquiv f M).trans
      (homLinearEquiv (M := of R (Module.Dual R ((restrictScalars f).obj (of S S)))) (N := M)
        (S := R)).symm).toModuleIso)
    (fun {M N} g ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun (x : (extendScalars f).obj M) ↦ ?_)
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | tmul s m =>
        refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
        change extendScalarsDualEquiv f N (s ⊗ₜ[R] g m) φ =
          g (extendScalarsDualEquiv f M (s ⊗ₜ[R] m) φ)
        rw [extendScalarsDualEquiv_tmul, extendScalarsDualEquiv_tmul, map_smul])

/-- Extension of scalars along a ring map `f : R →+* S` making `S` a finite projective
`R`-module preserves limits. -/
instance preservesLimits_extendScalars :
    PreservesLimits (extendScalars.{u, u, u} f) :=
  have : PreservesLimits (extendScalars.{u, u, u} f ⋙ restrictScalars.{u} f) :=
    preservesLimits_of_natIso (extendScalarsCompRestrictScalarsIso f).symm
  have : ReflectsLimits (restrictScalars.{u} f) := reflectsLimits_of_reflectsIsomorphisms
  preservesLimits_of_reflects_of_preserves _ (restrictScalars.{u} f)

section Dualizing

variable (δ : of S S ≅ (coextendScalars.{u, u, u} f).obj (of R R))

/-- For `S` finite projective over `R` with an `S`-linear identification
`δ : S ≅ Hom_R(S, R)`, the identification `S ⊗_R M ≅ Hom_R(S, M)`,
`s ⊗ m ↦ (x ↦ δ(s)(x) • m)`. -/
noncomputable def extendScalarsCoextendScalarsEquiv (M : ModuleCat.{u} R) :
    (extendScalars f).obj M ≃ₗ[S] (coextendScalars f).obj M :=
  let δR : (restrictScalars f).obj (of S S) ≃ₗ[R]
      Module.Dual R ((restrictScalars f).obj (of S S)) :=
      { toFun s := (δ.hom.hom (s : S) : (restrictScalars f).obj (of S S) →ₗ[R] R)
        invFun φ := (δ.inv.hom φ : S)
        map_add' := by simp
        map_smul' r s := by
          refine LinearMap.ext fun x ↦ ?_
          change (δ.hom.hom ((f r : S) • (s : S)) : _ →ₗ[R] R) x = r * (δ.hom.hom s : _ →ₗ[R] R) x
          rw [map_smul]
          change (δ.hom.hom s : (restrictScalars f).obj (of S S) →ₗ[R] R)
              (show (restrictScalars f).obj (of S S) from (show S from x) * f r) =
            r * (δ.hom.hom s : (restrictScalars f).obj (of S S) →ₗ[R] R) x
          rw [mul_comm]
          exact (δ.hom.hom s : (restrictScalars f).obj (of S S) →ₗ[R] R).map_smul r x
        left_inv s := by simp
        right_inv φ := by simp }
  let e := (TensorProduct.congr δR (LinearEquiv.refl R M)).trans (dualTensorHomEquiv R _ M)
  { e.toAddEquiv with
    map_smul' s x := by
      change e (s • x) = s • e x
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
      | tmul s' m =>
        refine CoextendScalars.ext (LinearMap.ext fun x ↦ ?_)
        change (δ.hom.hom (s * (show S from s')) : (restrictScalars f).obj (of S S) →ₗ[R] R) x • m =
          (δ.hom.hom s' : (restrictScalars f).obj (of S S) →ₗ[R] R)
            (show (restrictScalars f).obj (of S S) from (show S from x) * s) • m
        rw [← smul_eq_mul, map_smul]
        rfl }

/-- Extension and coextension of scalars agree along `f` when `S` is finite projective over `R`
and `Hom_R(S, R)` is identified with `S` by `δ`. -/
noncomputable def extendScalarsIsoCoextendScalars :
    extendScalars.{u, u, u} f ≅ coextendScalars.{u, u, u} f :=
  NatIso.ofComponents (fun M ↦ (extendScalarsCoextendScalarsEquiv f δ M).toModuleIso)
    (fun {M N} g ↦ by
      refine ModuleCat.hom_ext (LinearMap.ext fun (x : (extendScalars f).obj M) ↦ ?_)
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
      | tmul s m =>
        refine CoextendScalars.ext (LinearMap.ext fun x ↦ ?_)
        change (_ : R) • g m = g ((_ : R) • m)
        rw [map_smul]
        rfl)

end Dualizing
end ModuleCat

namespace CategoryTheory

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {R S : Type u} [CommRing R]
  [CommRing S] (f : R →+* S) [Module.Finite R ((ModuleCat.restrictScalars f).obj (.of S S))]
  [Module.Projective R ((ModuleCat.restrictScalars f).obj (.of S S))]

instance [UnivLE.{v₁, u}] [UnivLE.{max u₁ v₁, u}] :
    J.HasSheafCompose (ModuleCat.extendScalars.{u, u, u} f) :=
  have := preservesLimitsOfSize_of_univLE.{u, u, v₁, max u₁ v₁}
    (ModuleCat.extendScalars.{u, u, u} f)
  inferInstance

/-- Extension of scalars `− ⊗_R S` on sheaves of modules, for `S` finite projective over `R`. -/
noncomputable abbrev sheafExtendScalars [UnivLE.{v₁, u}] [UnivLE.{max u₁ v₁, u}] :
    Sheaf J (ModuleCat.{u} R) ⥤ Sheaf J (ModuleCat.{u} S) :=
  sheafCompose J (ModuleCat.extendScalars.{u, u, u} f)

end CategoryTheory
