/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ConstantModulePushforwardFunctoriality
import WeilConjectures.AlgebraicGeometry.ConstantModuleLimitFiberDescent
import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact

/-! # Surjectivity of the constant-module continuity comparison

Source: Stacks Project, Tag 09Z1, degree zero.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The constant-module continuity comparison is an epimorphism.

The arbitrary diagram `K` and cocone `c` are identified with the constant-module
pushforward diagram by `eK`, `hK`, `e` and `hι`. These hypotheses fix the transition
maps and comparison components; they do not assume a colimit property.
Only surjectivity is asserted, not the complementary injectivity assertion.

Source: Stacks Project, Tag 09Z1, degree-zero continuity and its canonical maps;
Tag 09Z6, finite approximation paragraph. -/
theorem epi_constantModulePushforwardComparison
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X : Scheme.{u}} {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) (p : ∀ i, D.obj i ⟶ X)
    (hp : ∀ {i j : I} (g : i ⟶ j), D.map g ≫ p j = p i)
    [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    [∀ i : I, QuasiCompact (p i)] [∀ i : I, QuasiSeparated (p i)]
    {Y : Scheme.{u}} (ν : Y ⟶ X)
    (π : (Functor.const I).obj Y ⟶ D) (hπ : ∀ i, π.app i ≫ p i = ν)
    [QuasiCompact ν] [QuasiSeparated ν]
    (hc : IsLimit (Cone.mk Y π))
    (K : Iᵒᵖ ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (eK : ∀ i : Iᵒᵖ, K.obj i ≅
      (lowerStar (ModuleCat.{u + 1} Λ) (p i.unop)).obj
        ((constantSheaf (D.obj i.unop).smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).obj M))
    (hK : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), K.map g =
      (eK i).hom ≫ constantModulePushforwardMap Λ M _ _ (D.map g.unop) (hp g.unop) ≫
        (eK j).inv)
    (c : Cocone K)
    (e : c.pt ≅ (lowerStar (ModuleCat.{u + 1} Λ) ν).obj
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M))
    (hι : ∀ i : Iᵒᵖ, c.ι.app i ≫ e.hom =
      (eK i).hom ≫ constantModulePushforwardMap Λ M _ _ (π.app i.unop) (hπ i.unop)) :
    Epi (colimit.desc K c) := by
  classical
  have _ := @hK
  apply (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale
    X (ModuleCat.{u + 1} Λ)).epi_of_epi_map
  rintro ⟨-, ⟨s⟩⟩
  let T := (X.uliftPointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
  apply (ModuleCat.epi_iff_surjective _).2
  intro x
  obtain ⟨i, y, hy⟩ := exists_constantModule_limit_fiber_rep
    Λ M D p hp ν π hπ hc s ((T.map e.hom) x)
  refine ⟨(T.map (colimit.ι K (op i))) ((T.map (eK (op i)).inv) y), ?_⟩
  apply (ModuleCat.mono_iff_injective (T.map e.hom)).1 inferInstance
  have hcomp : colimit.ι K (op i) ≫ colimit.desc K c ≫ e.hom =
      (eK (op i)).hom ≫ constantModulePushforwardMap Λ M _ _
        (π.app i) (hπ i) := by
    rw [colimit.ι_desc_assoc]
    exact hι (op i)
  have heq := congrArg (fun f => (T.map f) ((T.map (eK (op i)).inv) y)) hcomp
  simp only [Functor.map_comp, ModuleCat.comp_apply] at heq
  have hinv : (T.map (eK (op i)).hom) ((T.map (eK (op i)).inv) y) = y := by
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, Iso.inv_hom_id,
      T.map_id, ModuleCat.id_apply]
  rw [hinv] at heq
  simpa only [Functor.map_comp, ModuleCat.comp_apply] using heq.trans hy

end AlgebraicGeometry.Etale
