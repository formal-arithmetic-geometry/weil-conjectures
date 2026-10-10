/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.Adic.ForgetCoherence
public import WeilConjectures.WeilSheaf.StalkCharpoly

/-!
# Stalks of the pullback of a Weil sheaf

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes with base change `φ̄ : X̄ ⟶ Ȳ`, and `F` a Weil
sheaf on `Y`. The stalk of `φ^* F` at a geometric point `t` of `X̄` is the stalk of `F` at
`t ≫ φ̄`, compatibly with the Frobenius relative to `𝔽_{qᵐ}`
(`AlgebraicGeometry.WeilSheaf.nonempty_equiv_stalkAt_upperStar`). As a consequence pullback
preserves punctual purity (`AlgebraicGeometry.WeilSheaf.IsPunctuallyPureOfWeight.upperStar`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] (F : WeilSheaf k₀ l Y)

/-- The underlying sheaf of `φ^* F` is the pullback along `φ̄`. -/
lemma upperStar_obj_obj_carrier :
    ((upperStar φ).obj F).obj.carrier =
      (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].obj F.obj.carrier :=
  rfl


/-- The Weil structure of `φ^* F` is transported from that of `F`. -/
lemma upperStar_obj_obj_str :
    ((upperStar φ).obj F).obj.str =
      (ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l φ (comp_over φ (Spec (CommRingCat.of k₀)))).app
          F.obj.carrier ≪≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].mapIso F.obj.str :=
  Endofunctor.IsoAlgebra.mapOfNatIso_obj_str _ F.obj

private lemma frobeniusStr_upperStar_aux :
    ((upperStar φ).obj F).frobeniusStr =
      (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).hom.app
          ((upperStar φ).obj F).obj.carrier.X ≫
      (ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).inv.app
          ((Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].obj
            F.obj.carrier).X ≫
      (ProEtale.upperStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))).inv.app
          F.obj.carrier.X ≫
        (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).hom.app F.obj.carrier.X ≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*[_].map
          F.frobeniusStr := by
  rw [frobeniusStr, upperStar_obj_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  change _ ≫ ((ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso l φ
    (comp_over φ (Spec (CommRingCat.of k₀)))).hom.app F.obj.carrier ≫ _).hom = _
  rw [Mod.comp_hom', ProEtale.adicUpperStar_map_hom,
    ProEtale.adicUpperStarGeometricFiberMapCompFrobeniusIso_hom_app_hom]
  simp only [Category.assoc, frobeniusStr, Functor.map_comp]
  rfl

-- Stated for a variable isomorphism `α`: for `α = upperStarIsoLowerStarInv` the kernel times out
-- comparing the two objects, which agree only up to unfolding `upperStar`.
private lemma hom_inv_id_app_upperStar_assoc
    {P Q : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) ⥤
        Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (WeilCoefficients.{u} l)} (α : P ≅ Q) {Z} (h : P.obj
      ((Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].obj
        F.obj.carrier).X ⟶ Z) :
    α.hom.app ((upperStar φ).obj F).obj.carrier.X ≫
      α.inv.app ((Scheme.Hom.geometricFiberMap φ
        (comp_over φ (Spec (CommRingCat.of k₀))))^*ᵃ[l].obj F.obj.carrier).X ≫ h = h :=
  Iso.hom_inv_id_app_assoc α _ h

/-- The Weil structure of the pullback `φ^* F`, on the underlying sheaves: the pullback along `φ̄`
of the Weil structure of `F`, through `Fr_X^* φ̄^* ≅ (Fr_X ≫ φ̄)^* = (φ̄ ≫ Fr_Y)^* ≅ φ̄^* Fr_Y^*`.
-/
lemma frobeniusStr_upperStar :
    ((upperStar φ).obj F).frobeniusStr =
      (ProEtale.upperStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))).inv.app
          F.obj.carrier.X ≫
        (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app F.obj.carrier.X ≫
        (ProEtale.upperStarComp _
          (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).hom.app F.obj.carrier.X ≫
        (Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀))))^*[_].map
          F.frobeniusStr :=
  (frobeniusStr_upperStar_aux φ F).trans (hom_inv_id_app_upperStar_assoc φ F _ _)

end AlgebraicGeometry.WeilSheaf
