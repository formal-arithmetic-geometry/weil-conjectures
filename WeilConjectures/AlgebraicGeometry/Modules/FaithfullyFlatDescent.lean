/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.RingTheory.FaithfullyFlat.FamilyDescent

/-!
# Descent of morphisms of quasi-coherent modules along faithfully flat maps of affine schemes

Let `A → B` be a faithfully flat ring map and `f : Spec B ⟶ Spec A` the induced morphism. Pulling
back along `f` is fully faithful on quasi-coherent modules, in the sense of descent data: a
morphism `f^* M ⟶ f^* N` whose two pullbacks to `Spec (B ⊗[A] B)` agree comes from a unique
morphism `M ⟶ N`. On global sections this is Amitsur exactness
(`Module.FaithfullyFlat.exists_eq_one_tmul_of_rTensor_eq`).
-/

@[expose] public section

universe u

open CategoryTheory Opposite TensorProduct CategoryTheory.Bicategory

namespace AlgebraicGeometry.Scheme.Modules

section

variable {R : CommRingCat.{u}}

/-- Morphisms out of a quasi-coherent module on an affine scheme are determined by their effect
on global sections. -/
lemma hom_ext_of_isQuasicoherent_Spec {M Q : (Spec R).Modules} [M.IsQuasicoherent]
    {α β : M ⟶ Q} (h : ∀ m : Γ(M, ⊤), α.app ⊤ m = β.app ⊤ m) : α = β := by
  have : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  rw [← cancel_epi M.fromTildeΓ]
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  ext m
  change α.app ⊤ (M.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m)) =
    β.app ⊤ (M.fromTildeΓ.app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m))
  have e := fromTildeΓ_app_toOpen M m
  exact (congrArg (α.app ⊤) e).trans ((h m).trans (congrArg (β.app ⊤) e).symm)

/-- A linear map between the global sections of quasi-coherent modules on an affine scheme comes
from a morphism of modules. -/
lemma exists_hom_app_top_eq {M N : (Spec R).Modules} [M.IsQuasicoherent]
    [N.IsQuasicoherent] (χ : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) :
    ∃ φ : M ⟶ N, ∀ m : Γ(M, ⊤), φ.app ⊤ m = χ m := by
  have : IsIso M.fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent M
  refine ⟨inv M.fromTildeΓ ≫ tilde.map χ ≫ N.fromTildeΓ, fun m ↦ ?_⟩
  have hm : (inv M.fromTildeΓ).app ⊤ m = tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m := by
    have k : ∀ x, (inv M.fromTildeΓ).app ⊤ (M.fromTildeΓ.app ⊤ x) = x := fun x ↦
      congr($(IsIso.hom_inv_id M.fromTildeΓ).app ⊤ x)
    exact (congrArg ((inv M.fromTildeΓ).app ⊤) (fromTildeΓ_app_toOpen M m)).symm.trans (k _)
  change N.fromTildeΓ.app ⊤ ((tilde.map χ).app ⊤ ((inv M.fromTildeΓ).app ⊤ m)) = χ m
  rw [hm]
  have h₂ : (tilde.map χ).app ⊤ (tilde.toOpen (moduleSpecΓFunctor.obj M) ⊤ m) =
      tilde.toOpen (moduleSpecΓFunctor.obj N) ⊤ (χ m) :=
    congr($(tilde.toOpen_map_app χ ⊤) m)
  rw [h₂]
  exact fromTildeΓ_app_toOpen N (χ m)

end

section Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Morphisms out of the pullback of a quasi-coherent module along `Spec B ⟶ Spec A` are
determined by their values on the images of global sections under the unit. -/
lemma pullback_hom_ext_Spec {M : (Spec (.of A)).Modules} [M.IsQuasicoherent]
    {Q : (Spec (.of B)).Modules}
    {α β : (pullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj M ⟶ Q}
    (h : ∀ m : Γ(M, ⊤),
      α.app ⊤ (pullbackΓ (Spec.map (CommRingCat.ofHom (algebraMap A B))) M m) =
        β.app ⊤ (pullbackΓ (Spec.map (CommRingCat.ofHom (algebraMap A B))) M m)) :
    α = β := by
  apply hom_ext_of_isQuasicoherent_Spec (R := .of B)
  intro y
  obtain ⟨e, he⟩ := exists_linearEquiv_pullback_Spec (B := B) M
  obtain ⟨t, rfl⟩ := e.surjective y
  induction t using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul b m =>
    have : e (b ⊗ₜ m) = b • e (1 ⊗ₜ m) := by
      rw [← LinearEquiv.map_smul, smul_tmul', smul_eq_mul, mul_one]
    rw [this, he]
    exact (Hom.app_smul_of α ⊤ b _).trans
      ((congrArg (b • ·) (h m)).trans (Hom.app_smul_of β ⊤ b _).symm)
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

/-- The two morphisms `Spec (B ⊗[A] B) ⟶ Spec B`. -/
noncomputable abbrev specTensorFst (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (.of (B ⊗[A] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom)

/-- The two morphisms `Spec (B ⊗[A] B) ⟶ Spec B`. -/
noncomputable abbrev specTensorSnd (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (.of (B ⊗[A] B)) ⟶ Spec (.of B) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)

lemma specTensorFst_comp :
    specTensorFst A B ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) := by
  rw [← Spec.map_comp]
  congr 1

lemma specTensorSnd_comp :
    specTensorSnd A B ≫ Spec.map (CommRingCat.ofHom (algebraMap A B)) =
      Spec.map (CommRingCat.ofHom (algebraMap A (B ⊗[A] B))) := by
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_one_eq_one_tmul]

/-- On global sections over `Spec B`, the unit of the adjunction for `Spec C ⟶ Spec B` is
semilinear along the ring map. -/
lemma pullbackΓ_smul_ringHom {C : Type u} [CommRing C] (ι : B →+* C)
    (P : (Spec (.of B)).Modules) (b : B) (x : Γ(P, ⊤)) :
    pullbackΓ (Spec.map (CommRingCat.ofHom ι)) P (b • x) =
      ι b • pullbackΓ (Spec.map (CommRingCat.ofHom ι)) P x :=
  letI := ι.toAlgebra
  pullbackΓ_smul (A := B) (B := C) P b x

end Algebra

end AlgebraicGeometry.Scheme.Modules
