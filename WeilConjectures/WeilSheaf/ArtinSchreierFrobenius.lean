/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Fourier
public import WeilConjectures.WeilSheaf.StalkConstantSheaf

/-!
# The counit of the Artin–Schreier pushforward and the Frobenius

Let `ĀS : 𝔸¹_{k̄} ⟶ 𝔸¹_{k̄}` be the geometric Artin–Schreier map. The counit
`ε : ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` of `ĀS^* ⊣ ĀS_*`, which evaluates a function on the fibres of `ĀS`
at the given point of the fibre, is compatible with the Weil structures of `AS_* ℚ̄_ℓ` and of
`ℚ̄_ℓ` (`AlgebraicGeometry.affineLine.artinSchreierCounit_frobenius`), and its pullback along a
translation `σ̄_c` is the evaluation along `x ↦ (x, σ̄_c x)`
(`AlgebraicGeometry.affineLine.artinSchreierCounit_translation`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

open scoped ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

local notation "ĀS" => affineLine.geometricArtinSchreierMap k₀

variable (k₀ l) in
/-- The counit `ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` of `ĀS^* ⊣ ĀS_*` at the constant sheaf. -/
noncomputable abbrev affineLine.artinSchreierCounit :
    (ĀS)^*[WeilCoefficients.{u} l].obj ((ĀS)_*[WeilCoefficients.{u} l].obj
      (ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ⟶
      ProEtale.adicConstantSheaf l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber :=
  (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) ĀS).counit.app _

/-- The pushforward-level identity behind
`AlgebraicGeometry.affineLine.artinSchreierCounit_frobenius`. -/
lemma affineLine.lowerStar_map_adicConstantSheafToLowerStar_frobenius :
    (ĀS)_*[WeilCoefficients.{u} l].map (ProEtale.adicConstantSheafToLowerStar l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom) ≫
        (ProEtale.lowerStarFactor _ (rfl : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom ≫ ĀS = (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom ≫ ĀS)).hom.app
          (ProEtale.adicConstantSheaf l _) =
      (ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).unit.app _ ≫
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)_*[WeilCoefficients.{u} l].map
          (WeilSheaf.artinSchreierPushforward k₀ l).frobeniusStr ≫
        (ProEtale.lowerStarFactor _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          (affineLine.artinSchreierMap k₀) (comp_over _ _))).hom.app
          (ProEtale.adicConstantSheaf l _) := by
  sorry

/-- The counit `ε : ĀS^* ĀS_* ℚ̄_ℓ ⟶ ℚ̄_ℓ` is compatible with the Weil structures of `AS_* ℚ̄_ℓ`
and of `ℚ̄_ℓ`: in the form of the compatibility condition of
`AlgebraicGeometry.WeilSheaf.globalSectionsTransport_frobeniusPowStr_comp_stalkObjHomOfUpperStar`,
with the Weil structure of `ℚ̄_ℓ` the canonical morphism `Fr^* ℚ̄_ℓ ⟶ ℚ̄_ℓ`. -/
lemma affineLine.artinSchreierCounit_frobenius :
    (ProEtale.upperStarComp _ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom ĀS).hom.app (WeilSheaf.artinSchreierPushforward k₀ l).obj.carrier.X ≫
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map (affineLine.artinSchreierCounit k₀ l) ≫
        ProEtale.upperStarAdicConstantSheafHom l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          (affineLine.artinSchreierMap k₀) (comp_over _ _)).symm).hom.app
          (WeilSheaf.artinSchreierPushforward k₀ l).obj.carrier.X ≫
        (ProEtale.upperStarComp _ ĀS (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).hom.app
          (WeilSheaf.artinSchreierPushforward k₀ l).obj.carrier.X ≫
        (ĀS)^*[WeilCoefficients.{u} l].map
          (WeilSheaf.artinSchreierPushforward k₀ l).frobeniusStr ≫
        affineLine.artinSchreierCounit k₀ l := by
  apply ((ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l)
    ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom ≫ ĀS)).homEquiv _ _).injective
  have h₁ : ProEtale.upperStarAdicConstantSheafHom l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom =
      ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map (ProEtale.adicConstantSheafToLowerStar l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom) ≫
        (ProEtale.upperStarLowerStarAdjunction _ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).counit.app _ :=
    Adjunction.homEquiv_counit _ _ _ _
  have e₁ := ProEtale.homEquiv_upperStarFactor_hom_app_comp_counit
    (rfl : (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom ≫ ĀS = (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom ≫ ĀS) (WeilSheaf.artinSchreierPushforward k₀ l).obj.carrier.X
    (ProEtale.adicConstantSheaf l _)
    (affineLine.artinSchreierCounit k₀ l ≫ ProEtale.adicConstantSheafToLowerStar l (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)
  have e₂ := ProEtale.homEquiv_upperStarFactor_hom_app_comp_counit
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
      (affineLine.artinSchreierMap k₀) (comp_over _ _))
    (WeilSheaf.artinSchreierPushforward k₀ l).obj.carrier.X (ProEtale.adicConstantSheaf l _)
    (WeilSheaf.artinSchreierPushforward k₀ l).frobeniusStr
  rw [ProEtale.upperStarFactor_rfl, Functor.map_comp, Category.assoc, ← h₁] at e₁
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  rw [Functor.map_comp]
  erw [(ProEtale.upperStarLowerStarAdjunction (WeilCoefficients.{u} l) ĀS).right_triangle_components_assoc]
  exact affineLine.lowerStar_map_adicConstantSheafToLowerStar_frobenius

end AlgebraicGeometry
