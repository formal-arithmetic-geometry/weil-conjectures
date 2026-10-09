/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine
public import WeilConjectures.AlgebraicGeometry.Cohomology.LongExact
public import WeilConjectures.AlgebraicGeometry.Modules.PushforwardRestrict
public import WeilConjectures.Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# Cokernels and extensions of quasi-coherent modules

Let `X` be a scheme. We show that the quasi-coherent `𝒪_X`-modules are closed under cokernels and
extensions; together with `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel` they form an
abelian subcategory of `X.Modules` closed under extensions [Stacks, Tag 01IE].

The proofs reduce to the affine opens `Spec Γ(X, U) ⟶ X`. On `Spec R`, the quasi-coherent modules
are the essential image of `M ↦ M^~`, which is a fully faithful left adjoint, so it is closed under
cokernels. For an extension `0 → M₁ → M₂ → M₃ → 0` with `M₁` quasi-coherent, the sequences of
sections over the basic opens are short exact (`surjective_app_of_cechAcyclicOnAffines`), so `M₂`
is localizing when `M₁` and `M₃` are, localization being exact.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`: the cokernel of a morphism of
  quasi-coherent modules is quasi-coherent.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_X₂`: an extension of quasi-coherent modules is
  quasi-coherent.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- On `Spec R`, the cokernel of a morphism of modules of the form `M^~` is of this form: `M ↦ M^~`
is fully faithful and preserves cokernels. -/
theorem isIso_fromTildeΓ_cokernel {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [hM : IsIso M.fromTildeΓ] [hN : IsIso N.fromTildeΓ] (φ : M ⟶ N) :
    IsIso (cokernel φ).fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff] at hM hN ⊢
  obtain ⟨A, ⟨eA⟩⟩ := hM
  obtain ⟨B, ⟨eB⟩⟩ := hN
  let ψ : A ⟶ B := (tilde.functor R).preimage (eA.hom ≫ φ ≫ eB.inv)
  refine ⟨cokernel ψ, ⟨PreservesCokernel.iso (tilde.functor R) ψ ≪≫
    cokernel.mapIso ((tilde.functor R).map ψ) φ eA eB ?_⟩⟩
  rw [Functor.map_preimage]
  simp

/-- **The cokernel of a morphism of quasi-coherent modules is quasi-coherent.** On an affine open
`U`, restriction along `Spec Γ(X, U) ⟶ X` commutes with cokernels, and on `Spec Γ(X, U)` the
cokernel of a morphism of modules of the form `M^~` is of this form (`isIso_fromTildeΓ_cokernel`). -/
theorem isQuasicoherent_cokernel {M N : X.Modules}
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) N] (φ : M ⟶ N) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) (cokernel φ) := by
  refine isQuasicoherent_of_iSup_opensRange_eq_top (cokernel φ)
    (fun U : {U : X.Opens // IsAffineOpen U} ↦ U.2.fromSpec) iSup_opensRange_fromSpec_eq_top
    fun U ↦ ?_
  have : IsIso (cokernel ((restrictFunctor U.2.fromSpec).map φ)).fromTildeΓ :=
    isIso_fromTildeΓ_cokernel _
  let e := PreservesCokernel.iso (restrictFunctor U.2.fromSpec) φ
  haveI : IsIso (C := SheafOfModules.{u} (Spec Γ(X, U.1)).ringCatSheaf) e.inv :=
    (inferInstance : IsIso e.inv)
  exact (presentationOfIsIsoFromTildeΓ _).ofIsIso e.inv

section Extension

variable {R : CommRingCat.{u}}

/-- In a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of modules on `Spec R` with `M₁`
quasi-coherent, the sequence of sections over an affine open `U` is short exact. -/
lemma sections_shortExact_of_isQuasicoherent {S : ShortComplex (Spec R).Modules}
    (hS : S.ShortExact) [SheafOfModules.IsQuasicoherent (R := (Spec R).ringCatSheaf) S.X₁]
    {U : (Spec R).Opens} (hU : IsAffineOpen U) :
    Function.Injective ((modulesSpecToSheaf.map S.f).hom.app (op U)).hom ∧
      Function.Exact ((modulesSpecToSheaf.map S.f).hom.app (op U)).hom
        ((modulesSpecToSheaf.map S.g).hom.app (op U)).hom ∧
      Function.Surjective ((modulesSpecToSheaf.map S.g).hom.app (op U)).hom := by
  have hS' := shortExact_map_toSheaf hS
  refine ⟨TopCat.Sheaf.injective_app_f hS' (op U), fun y ↦ ⟨fun hy ↦ ?_, ?_⟩,
    surjective_app_of_cechAcyclicOnAffines hS'
      (cechAcyclicOnAffines_of_isQuasicoherent S.X₁) hU⟩
  · exact TopCat.Sheaf.exists_app_f_eq hS' (op U) y hy
  · rintro ⟨x, rfl⟩
    exact TopCat.Sheaf.app_g_app_f (S := S.map (toAb _)) (op U) x

/-- On `Spec R`, an extension of localizing modules is localizing, provided the kernel is
quasi-coherent: the sections over `D(f)` are an extension of the localized sections. -/
theorem isLocalizing_X₂ {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [SheafOfModules.IsQuasicoherent (R := (Spec R).ringCatSheaf) S.X₁]
    (h₁ : IsLocalizing (modulesSpecToSheaf.obj S.X₁))
    (h₃ : IsLocalizing (modulesSpecToSheaf.obj S.X₃)) :
    IsLocalizing (modulesSpecToSheaf.obj S.X₂) := by
  intro f
  have := h₁ f
  have := h₃ f
  let D := PrimeSpectrum.basicOpen f
  obtain ⟨-, hex, hsurj⟩ := sections_shortExact_of_isQuasicoherent hS (isAffineOpen_top _)
  obtain ⟨hinj', hex', -⟩ := sections_shortExact_of_isQuasicoherent hS
    (U := D) (IsAffineOpen.Spec_basicOpen f)
  have hu : ∀ s : Submonoid.powers f, IsUnit (algebraMap R
      (Module.End R ((modulesSpecToSheaf.obj S.X₂).obj.obj (op D))) s) := by
    rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact (isUnit_algebraMap_end_of_le_basicOpen (M := S.X₂) f le_rfl).pow n
  have n₁ (k : (modulesSpecToSheaf.obj S.X₁).obj.obj (op ⊤)) :
      ((modulesSpecToSheaf.obj S.X₂).obj.map D.leTop.op).hom
          (((modulesSpecToSheaf.map S.f).hom.app (op ⊤)).hom k) =
        ((modulesSpecToSheaf.map S.f).hom.app (op D)).hom
          (((modulesSpecToSheaf.obj S.X₁).obj.map D.leTop.op).hom k) := by
    have := (modulesSpecToSheaf.map S.f).hom.naturality D.leTop.op
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) k).symm
  have n₂ (k : (modulesSpecToSheaf.obj S.X₂).obj.obj (op ⊤)) :
      ((modulesSpecToSheaf.obj S.X₃).obj.map D.leTop.op).hom
          (((modulesSpecToSheaf.map S.g).hom.app (op ⊤)).hom k) =
        ((modulesSpecToSheaf.map S.g).hom.app (op D)).hom
          (((modulesSpecToSheaf.obj S.X₂).obj.map D.leTop.op).hom k) := by
    have := (modulesSpecToSheaf.map S.g).hom.naturality D.leTop.op
    exact (LinearMap.congr_fun (congrArg ModuleCat.Hom.hom this) k).symm
  exact IsLocalizedModule.of_exact_of_surjective (.powers f) _ _ _ hex hsurj hinj' hex' n₁ n₂ hu

/-- On `Spec R`, an extension of modules of the form `M^~` is of this form. -/
theorem isIso_fromTildeΓ_X₂ {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [IsIso S.X₁.fromTildeΓ] [IsIso S.X₃.fromTildeΓ] : IsIso S.X₂.fromTildeΓ := by
  have : SheafOfModules.IsQuasicoherent (R := (Spec R).ringCatSheaf) S.X₁ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ _).2 inferInstance
  rw [isIso_fromTildeΓ_iff_isLocalizing] at *
  exact isLocalizing_X₂ hS ‹_› ‹_›

end Extension

/-- **An extension of quasi-coherent modules is quasi-coherent** [Stacks, Tag 01IE]. On an affine
open `U`, restriction along `Spec Γ(X, U) ⟶ X` is exact, and on `Spec Γ(X, U)` an extension of
modules of the form `M^~` is of this form (`isIso_fromTildeΓ_X₂`). -/
theorem isQuasicoherent_X₂ {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₁]
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₃] :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) S.X₂ := by
  refine isQuasicoherent_of_iSup_opensRange_eq_top S.X₂
    (fun U : {U : X.Opens // IsAffineOpen U} ↦ U.2.fromSpec) iSup_opensRange_fromSpec_eq_top
    fun U ↦ ?_
  let S' := S.map (restrictFunctor U.2.fromSpec)
  have hS' : S'.ShortExact := hS.map_of_exact (restrictFunctor U.2.fromSpec)
  have : IsIso S'.X₁.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent (S.X₁.restrict _)
  have : IsIso S'.X₃.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent (S.X₃.restrict _)
  have : IsIso S'.X₂.fromTildeΓ := isIso_fromTildeΓ_X₂ hS'
  exact presentationOfIsIsoFromTildeΓ S'.X₂

end AlgebraicGeometry.Scheme.Modules
