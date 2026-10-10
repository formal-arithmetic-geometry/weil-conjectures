/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.Mod.Evaluation
public import WeilConjectures.WeilSheaf.Dual
public import WeilConjectures.WeilSheaf.StalkPairing

/-!
# The stalks of the dual of a lisse Weil sheaf

The evaluation `F^∨ ⊗ F ⟶ ℚ̄_ℓ` of the dual `F^∨ = [F, ℚ̄_ℓ]` of a Weil sheaf is compatible with
the Weil structures (`AlgebraicGeometry.WeilSheaf.dual_evaluation_str`), hence it induces a
pairing of the stalks compatible with the local Frobenius.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Limits

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

/-- The evaluation `F^∨ ⊗ F ⟶ ℚ̄_ℓ` is compatible with the Weil structures. -/
theorem dual_evaluation_str (F : WeilSheaf k₀ l X) (hF : F.IsLisse) :
    ((F.dual hF).obj.str.hom.hom ⊗ₘ F.obj.str.hom.hom) ≫
        Mod.evaluation F.obj.carrier (adicConstant k₀ l X).obj.carrier =
      μ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]
          (F.dual hF).obj.carrier.X F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          (Mod.evaluation F.obj.carrier (adicConstant k₀ l X).obj.carrier) ≫
        (adicConstant k₀ l X).obj.str.hom.hom := by
  have : (Mod.mapModComap (G := ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[
      WeilCoefficients.{u} l]) (adicConstantSheafToLowerStar l
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)).IsEquivalence :=
    isEquivalence_adicLowerStar l _
  have h := Mod.μ_comp_map_evaluation (adicConstantSheafToLowerStar l
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)
    (fun _ _ ↦ Functor.LaxBraided.braided _ _) F.obj.carrier (adicConstant k₀ l X).obj.carrier
  have hstr : (F.dual hF).obj.str.hom.hom =
      ((adicLowerStarCompIhomIso l (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv
        F.obj.carrier).inv.app (adicConstant k₀ l X).obj.carrier).hom ≫
      ((Mod.ihomMap F.obj.str.inv).app _).hom ≫
      ((ProEtale.AdicSheaf.ihom F.obj.carrier).map (adicConstant k₀ l X).obj.str.hom).hom := rfl
  have hφ : F.obj.str.hom.hom ≫ F.obj.str.inv.hom = 𝟙 _ := by
    rw [← Mod.comp_hom', Iso.hom_inv_id, Mod.id_hom']
  rw [hstr, tensorHom_def', comp_whiskerRight, comp_whiskerRight]
  simp only [Category.assoc]
  rw [Mod.evaluation_naturality F.obj.carrier (adicConstant k₀ l X).obj.str.hom,
    Mod.evaluation_ihomMap_assoc F.obj.str.inv]
  erw [← whisker_exchange_assoc, ← MonoidalCategory.whiskerLeft_comp_assoc, hφ,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]
  erw [reassoc_of% h]
  rfl

end AlgebraicGeometry.WeilSheaf
