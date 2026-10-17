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
    (upperStarComp _ _ _).symm ≪≫ upperStarCongr _ c ≪≫ upperStarComp _ _ _ ≪≫
    Functor.isoWhiskerRight (upperStarIsoLowerStarInv _ b) _

/-- The exchange isomorphism is monoidal, as a composite of monoidal isomorphisms. -/
instance isMonoidal_upperStarExchange_hom (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) : NatTrans.IsMonoidal (upperStarExchange l j a b c).hom := by
  dsimp only [upperStarExchange, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

set_option maxHeartbeats 2000000 in
lemma adicUpperStarExchange_hom_app_hom (j : T₁ ⟶ T₂) (a : T₁ ≅ T₁) (b : T₂ ≅ T₂)
    (c : a.hom ≫ j = j ≫ b.hom) (M : AdicSheaf l T₂) :
    ((adicUpperStarExchange l j a b c).hom.app M).hom =
      (upperStarExchange l j a b c).hom.app M.X := by
  simp only [adicUpperStarExchange, upperStarExchange, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarIsoLowerStarInv_inv_app_hom, adicUpperStarIsoLowerStarInv_hom_app_hom,
    adicUpperStarComp_inv_app_hom, adicUpperStarComp_hom_app_hom, adicUpperStarCongr_hom_app_hom]
  rfl

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

end AlgebraicGeometry.ProEtale
