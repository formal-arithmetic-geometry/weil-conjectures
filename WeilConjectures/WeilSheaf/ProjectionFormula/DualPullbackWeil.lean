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

namespace CategoryTheory

variable {D D' : Type*} [Category* D] [Category* D'] [MonoidalCategory D] [MonoidalCategory D']

/-- The algebra behind the compatibility of the comparison `j^* [G, 1] ⟶ [j^* G, 1]` with
structure morphisms, stated for evaluations `ev` and `ev'` in monoidal categories: if the
comparison `cc`, the structure morphisms `strG`, `sG` of `[G, 1]` and `G` and `strT` of
`[j^* G, 1]` are compatible with the evaluations, then so are `A cc ≫ strT` and
`E ≫ J strG ≫ cc`. -/
lemma whiskerRight_comp_evaluation_comm (J : D ⥤ D') (B : D ⥤ D) (A : D' ⥤ D')
    [J.LaxMonoidal] [B.LaxMonoidal] [A.LaxMonoidal] (E : J ⋙ A ⟶ B ⋙ J)
    (hEμ : ∀ X Y : D, μ A (J.obj X) (J.obj Y) ≫ A.map (μ J X Y) ≫ E.app (X ⊗ Y) =
      (E.app X ⊗ₘ E.app Y) ≫ μ J (B.obj X) (B.obj Y) ≫ J.map (μ B X Y))
    {Gh Gx One : D} {H' One' : D'} (ev : Gh ⊗ Gx ⟶ One) (ev' : H' ⊗ J.obj Gx ⟶ One')
    (strG : B.obj Gh ⟶ Gh) (sG : B.obj Gx ⟶ Gx) (Lb : B.obj One ⟶ One) (La : A.obj One' ⟶ One')
    (U : J.obj One ⟶ One') (cc : J.obj Gh ⟶ H') (strT : A.obj H' ⟶ H')
    (i : J.obj Gx ⟶ A.obj (J.obj Gx))
    (hi : i ≫ E.app Gx ≫ J.map sG = 𝟙 _)
    (hcc : cc ▷ J.obj Gx ≫ ev' = μ J Gh Gx ≫ J.map ev ≫ U)
    (hT : strT ▷ J.obj Gx ≫ ev' = A.obj H' ◁ i ≫ μ A H' (J.obj Gx) ≫ A.map ev' ≫ La)
    (hG : (strG ⊗ₘ sG) ≫ ev = μ B Gh Gx ≫ B.map ev ≫ Lb)
    (hEu : E.app One ≫ J.map Lb ≫ U = A.map U ≫ La) :
    (A.map cc ≫ strT) ▷ J.obj Gx ≫ ev' =
      ((E.app Gh ≫ J.map strG) ≫ cc) ▷ J.obj Gx ≫ ev' := by
  have hL : (A.map cc ≫ strT) ▷ J.obj Gx ≫ ev' =
      A.obj (J.obj Gh) ◁ i ≫ μ A (J.obj Gh) (J.obj Gx) ≫
        A.map (μ J Gh Gx ≫ J.map ev ≫ U) ≫ La := by
    rw [comp_whiskerRight_assoc, hT, ← whisker_exchange_assoc, μ_natural_left_assoc,
      ← A.map_comp_assoc, hcc]
  have hR : ((E.app Gh ≫ J.map strG) ≫ cc) ▷ J.obj Gx ≫ ev' =
      A.obj (J.obj Gh) ◁ i ≫ ((E.app Gh ≫ J.map strG) ⊗ₘ (E.app Gx ≫ J.map sG)) ≫
        μ J Gh Gx ≫ J.map ev ≫ U := by
    rw [comp_whiskerRight_assoc, hcc, tensorHom_def_assoc, ← whisker_exchange_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc, hi, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  have n := E.naturality ev
  simp only [Functor.comp_map] at n
  rw [hL, hR, ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, ← J.map_comp_assoc, hG]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (hEμ Gh Gx), ← reassoc_of% n, hEu]

end CategoryTheory

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

/-- **The comparison `j^* 𝓗om(G, ℚ̄_ℓ) ⟶ 𝓗om(j^* G, ℚ̄_ℓ)` is compatible with the structure
isomorphisms** induced by a structure isomorphism `s : (b⁻¹)_* G ≅ G`, transported along an
isomorphism `e` equal to the exchange isomorphism. -/
lemma adicUpperStarDualComparison_comm (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (e : (j)^*ᵃ[l] ⋙ (a.inv)_*ᵃ[l] ≅ (b.inv)_*ᵃ[l] ⋙ (j)^*ᵃ[l])
    (he : e = adicUpperStarExchange l j a b c) (G : AdicSheaf l T₂)
    (s : (b.inv)_*ᵃ[l].obj G ≅ G) :
    (a.inv)_*ᵃ[l].map (adicUpperStarDualComparison l j G) ≫
        ((adicLowerStarCompIhomIso l a.inv ((j)^*ᵃ[l].obj G)).inv.app (AdicSheaf.unit l T₁) ≫
          (Mod.ihomMap (e.app G ≪≫ (j)^*ᵃ[l].mapIso s).inv).app _ ≫
          (AdicSheaf.ihom ((j)^*ᵃ[l].obj G)).map (adicLowerStarUnitIso l a.symm).hom) =
      (e.hom.app ((AdicSheaf.ihom G).obj (AdicSheaf.unit l T₂)) ≫
        (j)^*ᵃ[l].map ((adicLowerStarCompIhomIso l b.inv G).inv.app (AdicSheaf.unit l T₂) ≫
          (Mod.ihomMap s.inv).app _ ≫
          (AdicSheaf.ihom G).map (adicLowerStarUnitIso l b.symm).hom)) ≫
        adicUpperStarDualComparison l j G := by
  obtain ⟨E, hE, h₁⟩ : ∃ E : (j)^*[WeilCoefficients.{u} l] ⋙ (a.inv)_*[WeilCoefficients.{u} l] ≅
      (b.inv)_*[WeilCoefficients.{u} l] ⋙ (j)^*[WeilCoefficients.{u} l],
      E = upperStarExchange l j a b c ∧ ∀ M, (e.hom.app M).hom = E.hom.app M.X :=
    ⟨_, rfl, fun M ↦ by
      subst he
      exact adicUpperStarExchange_hom_app_hom j a b c M⟩
  have hEμ (X Y : Sheaf (Scheme.ProEt.topology T₂) (WeilCoefficients.{u} l)) :=
    hE ▸ upperStarExchange_μ (l := l) j a b c X Y
  have hi : (e.app G ≪≫ (j)^*ᵃ[l].mapIso s).inv.hom ≫ E.hom.app G.X ≫
      (j)^*[WeilCoefficients.{u} l].map s.hom.hom = 𝟙 _ := by
    rw [← h₁, ← adicUpperStar_map_hom, ← Mod.comp_hom', ← Mod.comp_hom']
    exact congrArg Mod.Hom.hom (e.app G ≪≫ (j)^*ᵃ[l].mapIso s).inv_hom_id
  have hEu := upperStarExchange_hom_app_comp_upperStarAdicConstantSheafHom_of_eq j a b c E hE
  apply Mod.uncurryHom_injective
  rw [Mod.uncurryHom, Mod.uncurryHom]
  simp only [Mod.comp_hom']
  rw [h₁, adicUpperStar_map_hom, adicLowerStar_map_hom]
  exact whiskerRight_comp_evaluation_comm (j)^*[WeilCoefficients.{u} l]
    (b.inv)_*[WeilCoefficients.{u} l] (a.inv)_*[WeilCoefficients.{u} l] E.hom hEμ
    (Mod.evaluation G (AdicSheaf.unit l T₂))
    (Mod.evaluation ((j)^*ᵃ[l].obj G) (AdicSheaf.unit l T₁)) _ s.hom.hom
    (adicLowerStarUnitIso l b.symm).hom.hom (adicLowerStarUnitIso l a.symm).hom.hom
    (adicUpperStarUnitIso l j).hom.hom _ _ _ hi
    (uncurryHom_adicUpperStarDualComparison j G)
    (uncurryHom_ihomStr a.inv ((j)^*ᵃ[l].obj G) (AdicSheaf.unit l T₁) _ _)
    (ihomStr_tensorHom_comp_evaluation b.inv G (AdicSheaf.unit l T₂) s _) hEu.symm

end AlgebraicGeometry.ProEtale
