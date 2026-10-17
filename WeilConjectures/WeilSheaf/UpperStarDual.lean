/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.LisseDuality
public import WeilConjectures.WeilSheaf.UpperStarTensor

/-!
# Pullbacks of duals of lisse Weil sheaves

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes. The pullback of the constant pro-étale Weil sheaf
`ℚ̄_ℓ` is `ℚ̄_ℓ` (`AlgebraicGeometry.ProEtaleWeilSheaf.upperStarAdicConstantIso`), and the pullback
of the dual of a lisse Weil sheaf is the dual of its pullback
(`AlgebraicGeometry.WeilSheaf.upperStarDualIso`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal MonObj

namespace AlgebraicGeometry

open ProEtale Endofunctor

open scoped Obj

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

set_option hygiene false in
local notation "σX" => (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

set_option hygiene false in
local notation "σY" => (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

set_option hygiene false in
local notation "W" => WeilCoefficients.{u} l

/-- The Weil structure of the constant pro-étale Weil sheaf `ℚ̄_ℓ` preserves the unit section. -/
lemma adicConstant_one_str {S : Scheme.{u}} [S.Over (Spec (CommRingCat.of k₀))] :
    ε ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[W] ≫
        ((S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[W].map
          (η : 𝟙_ _ ⟶ adicConstantSheaf l (S ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
        (ProEtaleWeilSheaf.adicConstant k₀ l S).str.hom.hom =
        (η : 𝟙_ _ ⟶ adicConstantSheaf l (S ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  set e := (S ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.symm
  have : IsMonHom (adicConstantSheafLowerStarIso l e).inv :=
    inferInstanceAs (IsMonHom (adicConstantSheafToLowerStar l e.hom))
  have : IsMonHom (adicConstantSheafLowerStarIso l e).hom := by
    have : IsMonHom (inv (adicConstantSheafLowerStarIso l e).inv) := inferInstance
    rwa [IsIso.Iso.inv_inv] at this
  exact IsMonHom.one_hom (f := (adicConstantSheafLowerStarIso l e).hom)

/-- The unit section of the pullback of `ℚ̄_ℓ` is compatible with the Weil structure. -/
lemma upperStar_adicConstant_one_str :
    ε ((σX).inv)_*[W] ≫ ((σX).inv)_*[W].map (ε (φ̄)^*[W] ≫
        (φ̄)^*[W].map (η : 𝟙_ _ ⟶ adicConstantSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber)) ≫
        ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj (ProEtaleWeilSheaf.adicConstant k₀ l Y)).str.hom.hom =
      ε (φ̄)^*[W] ≫ (φ̄)^*[W].map
        (η : 𝟙_ _ ⟶ adicConstantSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
  set ιX := upperStarIsoLowerStarInv W σX
  set ιY := upperStarIsoLowerStarInv W σY
  set ψ := (upperStarComp W (σX).hom φ̄).symm ≪≫
    upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
      φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm ≪≫
    upperStarComp _ φ̄ (σY).hom
  have hψ : NatTrans.IsMonoidal ψ.hom := by
    simp only [ψ, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  set P := (ProEtaleWeilSheaf.upperStar k₀ l φ).obj (ProEtaleWeilSheaf.adicConstant k₀ l Y)
  have hs : P.str.hom.hom = ιX.inv.app _ ≫ frobeniusStr P := by
    rw [frobeniusStr, Iso.inv_hom_id_app_assoc]
  have hfs : frobeniusStr P = ψ.hom.app _ ≫
      (φ̄)^*[W].map (frobeniusStr (ProEtaleWeilSheaf.adicConstant k₀ l Y)) := by
    rw [frobeniusStr_upperStar]
    simp [ψ]
  have hY := adicConstant_one_str (k₀ := k₀) (l := l) (S := Y)
  have hιXY := NatTrans.IsMonoidal.unit (τ := ιY.hom)
  have hι := NatTrans.IsMonoidal.unit (τ := ιX.inv)
  have hψu := NatTrans.IsMonoidal.unit (τ := ψ.hom)
  simp only [Functor.LaxMonoidal.comp_ε, Functor.comp_map] at hψu
  have hYfs : ε ((σY).hom)^*[W] ≫ ((σY).hom)^*[W].map
      (η : 𝟙_ _ ⟶ adicConstantSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) ≫
      frobeniusStr (ProEtaleWeilSheaf.adicConstant k₀ l Y) =
        (η : 𝟙_ _ ⟶ adicConstantSheaf l (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber) := by
    rw [frobeniusStr]
    erw [ιY.hom.naturality_assoc]
    erw [reassoc_of% hιXY]
    exact hY
  rw [hs, hfs]
  rw [ιX.inv.naturality_assoc]
  erw [reassoc_of% hι]
  rw [Functor.map_comp_assoc, ψ.hom.naturality, reassoc_of% hψu, ← Functor.map_comp,
    ← Functor.map_comp, hYfs]
  rfl

end ProEtaleWeilSheaf

end AlgebraicGeometry
