/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.Cohomology.FlatAffineSectionRingTensor

/-! # Scalar reassociation on a cartesian affine open

Source: Stacks Project, Tag 02KG, the displayed tensor reassociation in its proof.
-/

@[expose] public section

universe u
open CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

private theorem tensor_reassociation_of_ringEquiv
    {R S A B N : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra A B]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    (β : S →+* B) (e : (A ⊗[R] S) ≃ₐ[A] B)
    (he : ∀ b : S, e (1 ⊗ₜ[R] b) = β b) :
    let : Module S (B ⊗[A] N) := Module.compHom _ β
    ∃ E : (S ⊗[R] N) ≃ₗ[S] (B ⊗[A] N),
      ∀ b n, E (b ⊗ₜ[R] n) = β b ⊗ₜ[A] n := by
  let : Module S (B ⊗[A] N) := Module.compHom _ β
  let E : (S ⊗[R] N) ≃+ (B ⊗[A] N) :=
    (TensorProduct.comm R S N).toAddEquiv |>.trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A N S).symm.toAddEquiv
      |>.trans (TensorProduct.congr (LinearEquiv.refl A N) e.toLinearEquiv).toAddEquiv
      |>.trans (TensorProduct.comm A N B).toAddEquiv
  have hE (b : S) (n : N) : E (b ⊗ₜ[R] n) = β b ⊗ₜ[A] n := by
    simp [E, he]
  have hsmul (c : S) (x : S ⊗[R] N) : E (c • x) = c • E x := by
    induction x using TensorProduct.inductionOn with
    | tmul b n =>
      rw [TensorProduct.smul_tmul', hE, hE]
      change β (c * b) ⊗ₜ[A] n = β c • (β b ⊗ₜ[A] n)
      rw [map_mul, TensorProduct.smul_tmul']
      rfl
    | add x y hx hy => simp [smul_add, hx, hy]
  exact ⟨{ E with map_smul' := hsmul }, hE⟩

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {X : Scheme.{u}}

/-- Reassociate scalar extension with the coefficient ring of a cartesian affine open.
This concerns the original section module only, and assumes no quasi-coherence.
Source: Stacks Project, Tag 02KG, proof of Lemma 30.5.1. -/
theorem exists_baseChange_affine_tensor_reassociation (f : X ⟶ Spec (.of R))
    (W : X.Opens) (hW : IsAffineOpen W) (M : X.Modules)
    (W' : (baseChangedScheme (S := S) f).Opens)
    (hW' : W' = baseChangeFst (S := S) f ⁻¹ᵁ W)
    (h : W' ≤ baseChangeFst (S := S) f ⁻¹ᵁ W) :
    let P := M.presheafModuleCat ⋙
      ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
    let β := (((baseChangedScheme (S := S) f).presheaf.map
      (homOfLE (le_top : W' ≤ ⊤)).op).hom).comp
      (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
    letI : Algebra Γ(X, W) Γ(baseChangedScheme (S := S) f, W') :=
      (baseChangeFst (S := S) f |>.appLE W W' h).hom.toAlgebra
    letI : Module S (TensorProduct Γ(X, W) Γ(baseChangedScheme (S := S) f, W')
        Γ(M, W)) := Module.compHom _ β
    ∃ e : TensorProduct R S (P.obj (op W)) ≃ₗ[S]
        TensorProduct Γ(X, W) Γ(baseChangedScheme (S := S) f, W') Γ(M, W),
      ∀ (b : S) (s : P.obj (op W)),
        e (b ⊗ₜ[R] s) = β b ⊗ₜ[Γ(X, W)] (show Γ(M, W) from s) := by
  let α := ((X.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom).comp
    (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
  let : Algebra R Γ(X, W) := α.toAlgebra
  let P := M.presheafModuleCat ⋙
    ModuleCat.restrictScalars (((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom)
  let β := (((baseChangedScheme (S := S) f).presheaf.map
    (homOfLE (le_top : W' ≤ ⊤)).op).hom).comp
    (((Scheme.ΓSpecIso (.of S)).inv ≫ (baseChangeSnd (S := S) f).appTop).hom)
  let : Algebra Γ(X, W) Γ(baseChangedScheme (S := S) f, W') :=
    (baseChangeFst (S := S) f |>.appLE W W' h).hom.toAlgebra
  let N := (ModuleCat.restrictScalars α).obj (M.val.obj (op W))
  let : Module Γ(X, W) N := inferInstanceAs (Module Γ(X, W) Γ(M, W))
  have : IsScalarTower R Γ(X, W) N :=
    IsScalarTower.of_compHom R Γ(X, W) Γ(M, W)
  obtain ⟨e, he⟩ := exists_baseChange_affine_sectionRing_tensor f W hW W' hW' h
  obtain ⟨E, hE⟩ := tensor_reassociation_of_ringEquiv (N := N) β e he
  let j : N ≃ₗ[R] (P.obj (op W)) :=
    (ModuleCat.restrictScalarsComp _ _ |>.app (M.val.obj (op W))).toLinearEquiv
  refine ⟨(j.symm.baseChange R S).trans E, ?_⟩
  intro b s
  dsimp only [LinearEquiv.trans_apply]
  exact (congrArg E (LinearEquiv.baseChange_tmul R S _ _ (e := j.symm) b s)).trans
    ((hE b (j.symm s)).trans (by rfl))

end AlgebraicGeometry.Scheme.Modules
