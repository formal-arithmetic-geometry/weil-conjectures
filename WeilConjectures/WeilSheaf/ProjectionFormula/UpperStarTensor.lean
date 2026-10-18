/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.IsoAlgebraTensor
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

instance preservesColimitsOfShape_mapModComap_adicConstantSheafToLowerStar (g : T₁ ⟶ T₁)
    [IsIso g] : PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} l]) (adicConstantSheafToLowerStar l g)) :=
  have : (Mod.mapModComap (G := (g)_*[WeilCoefficients.{u} l])
      (adicConstantSheafToLowerStar l g)).IsEquivalence :=
    isEquivalence_adicLowerStar l g
  inferInstance

instance preservesColimitsOfShape_mapModComap_adicUpperStarRingHom (j : T₁ ⟶ T₂) :
    PreservesColimitsOfShape WalkingParallelPair
      (Mod.mapModComap (G := (j)^*[WeilCoefficients.{u} l]) (adicUpperStarRingHom l j)) :=
  inferInstanceAs (PreservesColimitsOfShape WalkingParallelPair (j)^*ᵃ[l])

/-- The exchange isomorphism of `ℓ`-adic pullbacks along a base change with the Frobenius
pullbacks is that of the underlying sheaves. -/
lemma adicUpperStarGeometricFiberMapCompFrobeniusIso_hom_app_hom' {k : Type u} [Field k]
    [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)} {g : Y₀ ⟶ Spec (.of k)}
    (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f) (M : AdicSheaf l g.geometricFiber) :
    ((adicUpperStarGeometricFiberMapCompFrobeniusIso l φ h).hom.app M).hom =
      (upperStarExchange l (Scheme.Hom.geometricFiberMap φ h) f.geometricGaloisFrobenius
        g.geometricGaloisFrobenius
        (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ h).symm).hom.app M.X := by
  rw [adicUpperStarGeometricFiberMapCompFrobeniusIso_hom_app_hom, upperStarExchange_hom_app]
  congr 1

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "𝐒" => Spec (CommRingCat.of k₀)

set_option hygiene false in
local notation "bc[" f "]" =>
  Scheme.Hom.geometricFiberMap f (comp_over f (Spec (CommRingCat.of k₀)))

end AlgebraicGeometry
