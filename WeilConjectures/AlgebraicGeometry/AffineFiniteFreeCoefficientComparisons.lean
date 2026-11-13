/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import WeilConjectures.AlgebraicGeometry.AffineHomComparisonMaps
import WeilConjectures.AlgebraicGeometry.AffineHomComparisonFiniteFree

/-! # Finite-free affine Hom comparisons with coefficients

Source: Stacks Project, Tag 01HV, lemma-spec-sheaves (4)-(5), and
Tag 0BQZ, lemma-regular-immersion-ext, the displayed coefficient map. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Degreewise affine Hom comparisons are natural in boundaries and coefficients.
Source: Stacks Project, Tag 01HV, lemma-spec-sheaves (4)-(5), and Tag 0BQZ,
lemma-regular-immersion-ext, the displayed coefficient map. -/
theorem affine_finite_free_coefficient_comparisons
    {Y : Scheme.{u}} (U : Y.affineOpens)
    (K : ChainComplex (ModuleCat.{u} Γ(Y, U.1)) ℕ)
    (hfree : ∀ q : ℕ, Module.Free Γ(Y, U.1) (K.X q))
    (hfinite : ∀ q : ℕ, Module.Finite Γ(Y, U.1) (K.X q)) :
    let A := (Γ(Y, U.1) : Type u)
    let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
    ∃ e : ∀ (q : ℕ) (N : ModuleCat.{u} A),
        SheafOfModules.homObj (R := U.1.toScheme.toRingedSpace.sheaf)
          (T.obj (K.X q)) (T.obj N) ≅ T.obj (ModuleCat.of A (K.X q ⟶ N)),
      (∀ (q : ℕ) (N : ModuleCat.{u} A),
        SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
          (T.map (K.d (q + 1) q)) (𝟙 (T.obj N)) ≫ (e (q + 1) N).hom =
        (e q N).hom ≫ T.map (ModuleCat.ofHom (Linear.leftComp A N (K.d (q + 1) q)))) ∧
      (∀ (q : ℕ) (N N' : ModuleCat.{u} A) (g : N ⟶ N'),
        SheafOfModules.homObjMap (R := U.1.toScheme.toRingedSpace.sheaf)
          (𝟙 (T.obj (K.X q))) (T.map g) ≫ (e q N').hom =
        (e q N).hom ≫ T.map (ModuleCat.ofHom (Linear.rightComp A (K.X q) g))) := by
  classical
  dsimp only
  let T := tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom
  have hT : T.Additive := by
    have : (Scheme.Modules.restrictFunctor U.2.isoSpec.hom).Additive := ⟨by intros; rfl⟩
    infer_instance
  obtain ⟨c, hpre, hpost, hunit⟩ := exists_affine_hom_comparison_maps U
  have hc (q : ℕ) (N : ModuleCat.{u} Γ(Y, U.1)) : IsIso (c (K.X q) N) := by
    have := hfree q
    have := hfinite q
    exact affine_hom_comparison_isIso_of_finite_free U T hT c hpre hunit (K.X q) N
  have := hc
  refine ⟨fun q N ↦ (asIso (c (K.X q) N)).symm, ?_, ?_⟩
  · intro q N
    apply (cancel_mono (c (K.X (q + 1)) N)).1
    simp only [Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← hpre (K.X q) (K.X (q + 1)) N (K.d (q + 1) q)]
    simp
  · intro q N N' g
    apply (cancel_mono (c (K.X q) N')).1
    simp only [Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [← hpost (K.X q) N N' g]
    simp

end AlgebraicGeometry
