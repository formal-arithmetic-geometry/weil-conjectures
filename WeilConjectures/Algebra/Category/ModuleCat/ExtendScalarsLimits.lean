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
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Extension of scalars along a finite projective ring map preserves limits

If `S` is finite projective as an `R`-module via `f : R →+* S`, then `S ⊗_R M ≅ Hom_R(S^∨, M)`
naturally in `M`, so `restrictScalars f ∘ extendScalars f` is a right adjoint, hence preserves
limits; since `restrictScalars f` preserves and reflects limits, so does `extendScalars f`
(`ModuleCat.preservesLimits_extendScalars`).
-/

@[expose] public noncomputable section

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

/-- If `R → S` is a map of domains making `S` a finite free `R`-module and `S` is a
principal ideal ring, then `Hom_R(S, R)` is free of rank one over `S`. -/
theorem nonempty_iso_coextendScalars_obj [IsDomain R] [IsDomain S] [IsPrincipalIdealRing S]
    [Module.Free R ((restrictScalars f).obj (of S S))] :
    Nonempty (of S S ≅ (coextendScalars.{u, u, u} f).obj (of R R)) := by
  let S' := (restrictScalars f).obj (of S S)
  let D := (coextendScalars.{u, u, u} f).obj (of R R)
  let : Algebra R S := f.toAlgebra
  let : Module R D := inferInstanceAs (Module R (Module.Dual R S'))
  have : Module.Free R S := inferInstanceAs (Module.Free R S')
  have : Module.Finite R S := inferInstanceAs (Module.Finite R S')
  have : IsScalarTower R S D := .of_algebraMap_smul fun r φ ↦ by
    refine CoextendScalars.ext (LinearMap.ext fun x ↦ ?_)
    let φ' : S →ₗ[R] R := (φ : S' →ₗ[R] R)
    change φ' ((fun y : S ↦ y * f r) x) = r * φ' x
    exact (congrArg φ' (mul_comm _ _)).trans (φ'.map_smul r x)
  have : Module.Finite R D := inferInstanceAs (Module.Finite R (Module.Dual R S'))
  have : Module.Finite S D := .of_restrictScalars_finite R S D
  have : Module.IsTorsionFree S D := .of_smul_eq_zero fun s φ h ↦ by
    by_contra! hne
    obtain ⟨r, hr, t, ht⟩ :=
      (Algebra.IsIntegral.isIntegral (R := R) s).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hne.1)
    let φ' : S →ₗ[R] R := (φ : S' →ₗ[R] R)
    have key : ∀ y : S, φ' (y * s) = 0 := fun y ↦ by
      have := congrArg (fun ψ : D ↦ ((ψ : S' →ₗ[R] R) : S →ₗ[R] R) y) h
      exact this
    refine hne.2 (CoextendScalars.ext (LinearMap.ext fun x ↦ ?_))
    change φ' (id x) = 0
    have hx := key (t * (id x : S))
    rw [show t * (id x : S) * s = r • (id x : S) by rw [Algebra.smul_def, ht]; ring, map_smul,
      smul_eq_mul, mul_eq_zero] at hx
    exact hx.resolve_left hr
  have : Module.Free S D := Module.free_of_finite_type_torsion_free'
  have hD : Module.finrank R D = Module.finrank R S :=
    (Module.finrank_eq_card_basis ((Module.Free.chooseBasis R S').dualBasis)).trans
      (Module.finrank_eq_card_basis (Module.Free.chooseBasis R S')).symm
  have hS : 0 < Module.finrank R S := Module.finrank_pos
  have h1 : Module.finrank S D = 1 := by
    have := Module.finrank_mul_finrank R S D
    rw [hD] at this
    exact (Nat.mul_eq_left hS.ne').mp this
  exact ⟨((Module.finBasisOfFinrankEq S D h1).equivFun.trans
    (LinearEquiv.funUnique (Fin 1) S S)).symm.toModuleIso⟩
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
