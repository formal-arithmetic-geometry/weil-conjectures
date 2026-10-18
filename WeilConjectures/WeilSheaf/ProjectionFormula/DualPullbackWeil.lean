/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.ProjectionFormula.UpperStarConstant
public import WeilConjectures.WeilSheaf.ProjectionFormula.LisseDualPullback
/-!
# Structure isomorphisms of internal homs and evaluations

For an automorphism `g` and sheaves `M`, `N` of `ℚ̄_ℓ`-modules with structure morphisms
`s : g_* M ≅ M` and `t : g_* N ⟶ N`, the induced structure morphism
`g_* 𝓗om(M, N) ≅ 𝓗om(g_* M, g_* N) ⟶ 𝓗om(M, N)` is determined by its composite with the
evaluation (`AlgebraicGeometry.ProEtale.uncurryHom_ihomStr`,
`AlgebraicGeometry.ProEtale.ihomStr_tensorHom_comp_evaluation`). These are the inputs for the
compatibility of the comparison `j^* 𝓗om(G, ℚ̄_ℓ) ⟶ 𝓗om(j^* G, ℚ̄_ℓ)` with Weil structures.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal Endofunctor

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T T₁ T₂ : Scheme.{u}}

attribute [local instance] Sheaf.symmetricCategory

/-- The comparison `g_* 𝓗om(M, N) ≅ 𝓗om(g_* M, g_* N)` along an automorphism `g` is compatible
with the evaluations. -/
lemma uncurryHom_adicLowerStarCompIhomIso_inv_app (g : T ⟶ T) [IsIso g] (M N : AdicSheaf l T) :
    Mod.uncurryHom ((adicLowerStarCompIhomIso l g M).inv.app N) =
      μ (g)_*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (g)_*[WeilCoefficients.{u} l].map (Mod.evaluation M N) := by
  have : (Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l g)).IsEquivalence :=
    isEquivalence_adicLowerStar l g
  exact (Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l g)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) M N).symm

/-- The structure morphism of `𝓗om(M, N)` induced by structure isomorphisms `s : g_* M ≅ M` and
`t : g_* N ⟶ N` is compatible with the evaluations. -/
lemma uncurryHom_ihomStr (g : T ⟶ T) [IsIso g] (M N : AdicSheaf l T) (s : (g)_*ᵃ[l].obj M ≅ M)
    (t : (g)_*ᵃ[l].obj N ⟶ N) :
    Mod.uncurryHom ((adicLowerStarCompIhomIso l g M).inv.app N ≫ (Mod.ihomMap s.inv).app _ ≫
        (AdicSheaf.ihom M).map t) =
      _ ◁ s.inv.hom ≫ μ (g)_*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (g)_*[WeilCoefficients.{u} l].map (Mod.evaluation M N) ≫ t.hom := by
  rw [← Category.assoc, Mod.uncurryHom_comp_ihom_map, Mod.uncurryHom_comp_ihomMap,
    uncurryHom_adicLowerStarCompIhomIso_inv_app, Category.assoc, Category.assoc]
  rfl

/-- The structure morphism of `𝓗om(M, N)` induced by structure isomorphisms `s : g_* M ≅ M` and
`t : g_* N ⟶ N`, tensored with `s`, followed by the evaluation. -/
lemma ihomStr_tensorHom_comp_evaluation (g : T ⟶ T) [IsIso g] (M N : AdicSheaf l T)
    (s : (g)_*ᵃ[l].obj M ≅ M) (t : (g)_*ᵃ[l].obj N ⟶ N) :
    (((adicLowerStarCompIhomIso l g M).inv.app N ≫ (Mod.ihomMap s.inv).app _ ≫
        (AdicSheaf.ihom M).map t).hom ⊗ₘ s.hom.hom) ≫ Mod.evaluation M N =
      μ (g)_*[WeilCoefficients.{u} l] ((AdicSheaf.ihom M).obj N).X M.X ≫
        (g)_*[WeilCoefficients.{u} l].map (Mod.evaluation M N) ≫ t.hom := by
  have h := uncurryHom_ihomStr g M N s t
  rw [Mod.uncurryHom] at h
  have hs : s.hom.hom ≫ s.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [tensorHom_def', Category.assoc, h]
  erw [← MonoidalCategory.whiskerLeft_comp_assoc, hs]
  rw [
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

end AlgebraicGeometry.ProEtale
