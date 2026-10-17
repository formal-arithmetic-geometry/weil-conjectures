/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseInternalHom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.MonoidalIso
public import WeilConjectures.WeilSheaf.TensorHomAdjunction
public import WeilConjectures.WeilSheaf.UpperStarComp

/-!
# Pullback of pro-étale Weil sheaves is compatible with tensor products

-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime] {T₁ T₂ : Scheme.{u}}

attribute [local instance] Sheaf.symmetricCategory

variable (l) in
/-- The exchange isomorphism `j^* ⋙ (a⁻¹)_* ≅ (b⁻¹)_* ⋙ j^*` of sheaves of `ℚ̄_ℓ`-modules
attached to a morphism `j` intertwining automorphisms `a` and `b`: through `a^* ≅ (a⁻¹)_*`, it
is `a^* j^* ≅ (a ≫ j)^* = (j ≫ b)^* ≅ j^* b^*`. -/
noncomputable def upperStarExchange (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) :
    (j)^*[WeilCoefficients.{u} l] ⋙ (a.inv)_*[WeilCoefficients.{u} l] ≅
      (b.inv)_*[WeilCoefficients.{u} l] ⋙ (j)^*[WeilCoefficients.{u} l] :=
  Functor.isoWhiskerLeft _ (upperStarIsoLowerStarInv _ a).symm ≪≫
    (upperStarComp _ a.hom j).symm ≪≫ upperStarCongr _ c ≪≫ upperStarComp _ j b.hom ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv _ b) _

/-- The exchange isomorphism is monoidal, as a composite of monoidal isomorphisms. -/
instance isMonoidal_upperStarExchange_hom (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) : NatTrans.IsMonoidal (upperStarExchange l j a b c).hom := by
  dsimp only [upperStarExchange, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance


lemma upperStarExchange_hom_app (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (M : Sheaf (Scheme.ProEt.topology T₂) (WeilCoefficients.{u} l)) :
    (upperStarExchange l j a b c).hom.app M =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.app
          ((j)^*[WeilCoefficients.{u} l].obj M) ≫
        (upperStarComp _ a.hom j).inv.app M ≫ (upperStarCongr _ c).hom.app M ≫
        (upperStarComp _ j b.hom).hom.app M ≫
        (j)^*[WeilCoefficients.{u} l].map
          ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l) b).hom.app M) := by
  have e : (upperStarExchange l j a b c).hom =
      Functor.whiskerLeft (j)^*[WeilCoefficients.{u} l]
        (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv ≫
      (upperStarComp (WeilCoefficients.{u} l) a.hom j).inv ≫
      (upperStarCongr (WeilCoefficients.{u} l) c).hom ≫
      (upperStarComp (WeilCoefficients.{u} l) j b.hom).hom ≫
      Functor.whiskerRight (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) b).hom
        (j)^*[WeilCoefficients.{u} l] := rfl
  rw [e, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]

/-- The exchange isomorphism of `ℓ`-adic sheaves, on the underlying sheaves. -/
lemma adicUpperStarExchange_hom_app_hom' (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (M : AdicSheaf l T₂) :
    ((adicUpperStarExchange l j a b c).hom.app M).hom =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) a).inv.app
          ((j)^*ᵃ[l].obj M).X ≫
        (upperStarComp _ a.hom j).inv.app M.X ≫ (upperStarCongr _ c).hom.app M.X ≫
        (upperStarComp _ j b.hom).hom.app M.X ≫
        (j)^*[WeilCoefficients.{u} l].map
          ((upperStarIsoLowerStarInv (WeilCoefficients.{u} l) b).hom.app M.X) := by
  simp only [adicUpperStarExchange, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarIsoLowerStarInv_inv_app_hom, adicUpperStarIsoLowerStarInv_hom_app_hom,
    adicUpperStarComp_inv_app_hom, adicUpperStarComp_hom_app_hom, adicUpperStarCongr_hom_app_hom]

/-- The exchange isomorphism of `ℓ`-adic sheaves is that of the underlying sheaves. -/
lemma adicUpperStarExchange_hom_app_hom (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (M : AdicSheaf l T₂) :
    ((adicUpperStarExchange l j a b c).hom.app M).hom =
      (upperStarExchange l j a b c).hom.app M.X := by
  rw [adicUpperStarExchange_hom_app_hom', upperStarExchange_hom_app]
  congr 1

/-- The quotient map `P ⊗ M ⟶ P ⊗_{ℚ̄_ℓ} M` is compatible with the comparison
`g^*(P ⊗_{ℚ̄_ℓ} M) ≅ g^*P ⊗_{ℚ̄_ℓ} g^*M`. -/
@[reassoc]
lemma adicUpperStar_map_tensorπ_comp_tensorLeftIso_hom {Y Z : Scheme.{u}} (g : Z ⟶ Y)
    (P M : AdicSheaf l Y) :
    (g)^*[WeilCoefficients.{u} l].map (Mod.tensorπ P M) ≫
        ((adicUpperStarTensorLeftIso l g M).hom.app P).hom =
      inv (μ (g)^*[WeilCoefficients.{u} l] P.X M.X) ≫
        Mod.tensorπ ((g)^*ᵃ[l].obj P) ((g)^*ᵃ[l].obj M) := by
  have : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l g)) :=
    inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (g)^*ᵃ[l])
  exact Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicUpperStarRingHom l g)
    (fun _ _ ↦ Adjunction.μ_comp_map_braiding (upperStarLowerStarAdjunction _ g) _ _) P M

/-- The quotient map `P ⊗ M ⟶ P ⊗_{ℚ̄_ℓ} M` is compatible with the comparison
`g_*(P ⊗_{ℚ̄_ℓ} M) ≅ g_*P ⊗_{ℚ̄_ℓ} g_*M` along an automorphism `g`. -/
@[reassoc]
lemma adicLowerStar_map_tensorπ_comp_tensorLeftIso_hom {X : Scheme.{u}} (g : X ⟶ X) [IsIso g]
    (P M : AdicSheaf l X) :
    (g)_*[WeilCoefficients.{u} l].map (Mod.tensorπ P M) ≫
        ((adicLowerStarTensorLeftIso l g M).hom.app P).hom =
      inv (μ (g)_*[WeilCoefficients.{u} l] P.X M.X) ≫
        Mod.tensorπ ((g)_*ᵃ[l].obj P) ((g)_*ᵃ[l].obj M) := by
  have : (Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l g)).IsEquivalence :=
    isEquivalence_adicLowerStar l g
  exact Mod.map_tensorπ_comp_tensorLeftCompMapModComapIso_hom (adicConstantSheafToLowerStar l g)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) P M

/-- Two morphisms out of `g_* j^*(P ⊗_{ℚ̄_ℓ} M)`, for an automorphism `g`, agreeing on
`g_* j^* P ⊗ g_* j^* M` are equal. -/
lemma adicLowerStar_upperStar_tensor_hom_ext (j : T₁ ⟶ T₂) (g : T₁ ⟶ T₁) [IsIso g]
    {P M : AdicSheaf l T₂} {N : AdicSheaf l T₁}
    {f₁ f₂ : (g)_*ᵃ[l].obj ((j)^*ᵃ[l].obj ((Mod.tensorLeft M).obj P)) ⟶ N}
    (h : μ (g)_*[WeilCoefficients.{u} l] ((j)^*[WeilCoefficients.{u} l].obj P.X)
          ((j)^*[WeilCoefficients.{u} l].obj M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map (μ (j)^*[WeilCoefficients.{u} l] P.X M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map ((j)^*[WeilCoefficients.{u} l].map
          (Mod.tensorπ P M)) ≫ f₁.hom =
      μ (g)_*[WeilCoefficients.{u} l] ((j)^*[WeilCoefficients.{u} l].obj P.X)
          ((j)^*[WeilCoefficients.{u} l].obj M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map (μ (j)^*[WeilCoefficients.{u} l] P.X M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map ((j)^*[WeilCoefficients.{u} l].map
          (Mod.tensorπ P M)) ≫ f₂.hom) :
    f₁ = f₂ := by
  let Φ := (g)_*ᵃ[l].mapIso ((adicUpperStarTensorLeftIso l j M).app P) ≪≫
    (adicLowerStarTensorLeftIso l g ((j)^*ᵃ[l].obj M)).app ((j)^*ᵃ[l].obj P)
  have hΦ : μ (g)_*[WeilCoefficients.{u} l] ((j)^*[WeilCoefficients.{u} l].obj P.X)
          ((j)^*[WeilCoefficients.{u} l].obj M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map (μ (j)^*[WeilCoefficients.{u} l] P.X M.X) ≫
        (g)_*[WeilCoefficients.{u} l].map ((j)^*[WeilCoefficients.{u} l].map
          (Mod.tensorπ P M)) ≫ Φ.hom.hom =
        Mod.tensorπ ((g)_*ᵃ[l].obj ((j)^*ᵃ[l].obj P)) ((g)_*ᵃ[l].obj ((j)^*ᵃ[l].obj M)) := by
    simp only [Φ, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Mod.comp_hom',
      adicLowerStar_map_hom]
    have h₁ : μ (j)^*[WeilCoefficients.{u} l] P.X M.X ≫
        (j)^*[WeilCoefficients.{u} l].map (Mod.tensorπ P M) ≫
          ((adicUpperStarTensorLeftIso l j M).hom.app P).hom =
        Mod.tensorπ ((j)^*ᵃ[l].obj P) ((j)^*ᵃ[l].obj M) := by
      rw [adicUpperStar_map_tensorπ_comp_tensorLeftIso_hom, IsIso.hom_inv_id_assoc]
    have h₂ := adicLowerStar_map_tensorπ_comp_tensorLeftIso_hom (l := l) g ((j)^*ᵃ[l].obj P)
      ((j)^*ᵃ[l].obj M)
    rw [← Functor.map_comp_assoc (g)_*[WeilCoefficients.{u} l] _
      ((adicUpperStarTensorLeftIso l j M).hom.app P).hom,
      ← Functor.map_comp_assoc (g)_*[WeilCoefficients.{u} l] (μ _ _ _), h₁]
    exact (congrArg (_ ≫ ·) h₂).trans (IsIso.hom_inv_id_assoc _ _)
  rw [← Φ.hom_inv_id_assoc f₁, ← Φ.hom_inv_id_assoc f₂]
  congr 1
  refine Mod.tensorLeft_obj_hom_ext ?_
  rw [← hΦ, Mod.comp_hom', Mod.comp_hom']
  simp only [Category.assoc]
  have hh : Φ.hom.hom ≫ Φ.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Φ.hom_inv_id]
    rfl
  rw [reassoc_of% hh, reassoc_of% hh]
  exact h

end AlgebraicGeometry.ProEtale
