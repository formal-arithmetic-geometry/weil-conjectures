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
public import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction

/-!
# Pullbacks of pro-étale Weil sheaves and tensor products

Let `φ : X ⟶ Y` be a morphism of `k₀`-schemes. The pullback `φ^*` of pro-étale Weil sheaves is
compatible with tensor products: the isomorphism `φ^*(P ⊗ M) ≅ φ^* P ⊗ φ^* M` of the underlying
sheaves of `ℚ̄_ℓ,X̄`-modules intertwines the Weil structures
(`AlgebraicGeometry.ProEtaleWeilSheaf.tensorFunctorCompUpperStarIso`).

The Weil structure `Fr_X^* φ^* P ≅ φ^* P` of a pullback is transported from that of `P` along
`Fr_X^* φ̄^* ≅ (φ̄ ≫ Fr_Y)^* ≅ φ̄^* Fr_Y^*`, a composite of monoidal isomorphisms of pullback functors
(`AlgebraicGeometry.ProEtaleWeilSheaf.frobeniusStr_upperStar`). Hence the pullback of a pairing
compatible with the Weil structures is again compatible with the Weil structures
(`AlgebraicGeometry.ProEtaleWeilSheaf.upperStar_pairing_str`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Limits Functor.LaxMonoidal

namespace AlgebraicGeometry

open ProEtale Endofunctor

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]

namespace ProEtaleWeilSheaf

section FrobeniusStr

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "Fr" =>
  ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[WeilCoefficients.{u} l]

set_option hygiene false in
local notation "Fr'" =>
  ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l]

set_option hygiene false in
local notation "ι" => upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
  (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

/-- The Weil structure `Fr^* P ⟶ P` of a pro-étale Weil sheaf on the underlying sheaf of
`ℚ̄_ℓ`-modules, with `Fr^*` the pullback along the geometric Frobenius. -/
noncomputable def frobeniusStr (P : ProEtaleWeilSheaf k₀ l X) : (Fr').obj P.carrier.X ⟶ P.carrier.X :=
  (ι).hom.app P.carrier.X ≫ P.str.hom.hom

/-- A pairing is compatible with the Weil structures in the pushforward form `Fr^* = (Fr⁻¹)_*` if
and only if it is in the pullback form. -/
lemma pairing_str_iff (P Q R : ProEtaleWeilSheaf k₀ l X)
    (e : P.carrier.X ⊗ Q.carrier.X ⟶ R.carrier.X) :
    (P.str.hom.hom ⊗ₘ Q.str.hom.hom) ≫ e = μ Fr _ _ ≫ (Fr).map e ≫ R.str.hom.hom ↔
      (frobeniusStr P ⊗ₘ frobeniusStr Q) ≫ e = μ Fr' _ _ ≫ (Fr').map e ≫ frobeniusStr R := by
  have hμ := NatTrans.IsMonoidal.tensor (τ := (ι).hom) P.carrier.X Q.carrier.X
  have hn := (ι).hom.naturality e
  simp only [Functor.comp_map] at hn
  rw [frobeniusStr, frobeniusStr, frobeniusStr, ← tensorHom_comp_tensorHom_assoc]
  constructor
  · intro h
    rw [h, reassoc_of% hμ, reassoc_of% hn]
  · intro h
    rw [← cancel_epi ((ι).hom.app P.carrier.X ⊗ₘ (ι).hom.app Q.carrier.X), h, ← reassoc_of% hμ,
      ← reassoc_of% hn]

end FrobeniusStr

section UpperStar

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))]

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

set_option hygiene false in
local notation "σX" => (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

set_option hygiene false in
local notation "σY" => (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius

private lemma frobeniusStr_upperStar_aux (P : ProEtaleWeilSheaf k₀ l Y) :
    frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P) =
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) σX).hom.app
          ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P).carrier.X ≫
      (upperStarIsoLowerStarInv (WeilCoefficients.{u} l) σX).inv.app
          ((φ̄)^*ᵃ[l].obj P.carrier).X ≫
      (upperStarComp _ σX.hom φ̄).inv.app P.carrier.X ≫
        (upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app P.carrier.X ≫
        (upperStarComp _ φ̄ σY.hom).hom.app P.carrier.X ≫
        (φ̄)^*[_].map (frobeniusStr P) := by
  rw [frobeniusStr, show ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P).str = _ from
    IsoAlgebra.mapOfNatIso_obj_str _ P, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  change _ ≫ ((adicUpperStarGeometricFiberMapCompFrobeniusIso l φ
    (comp_over φ (Spec (CommRingCat.of k₀)))).hom.app P.carrier ≫ _).hom = _
  rw [Mod.comp_hom', adicUpperStar_map_hom,
    adicUpperStarGeometricFiberMapCompFrobeniusIso_hom_app_hom]
  simp only [Category.assoc, frobeniusStr, Functor.map_comp]
  rfl

private lemma hom_inv_id_app_upperStar_assoc
    {F G : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l) ⥤
        Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
          (WeilCoefficients.{u} l)} (α : F ≅ G) (P : ProEtaleWeilSheaf k₀ l Y) {Z}
    (h : F.obj ((φ̄)^*ᵃ[l].obj P.carrier).X ⟶ Z) :
    α.hom.app ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P).carrier.X ≫
      α.inv.app ((φ̄)^*ᵃ[l].obj P.carrier).X ≫ h = h :=
  Iso.hom_inv_id_app_assoc α _ h

/-- The Weil structure of the pullback `φ^* P`, in pullback form: the pullback along `φ̄` of that
of `P`, through `Fr_X^* φ̄^* ≅ (Fr_X ≫ φ̄)^* = (φ̄ ≫ Fr_Y)^* ≅ φ̄^* Fr_Y^*`. -/
lemma frobeniusStr_upperStar (P : ProEtaleWeilSheaf k₀ l Y) :
    frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P) =
      (upperStarComp _ σX.hom φ̄).inv.app P.carrier.X ≫
        (upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app P.carrier.X ≫
        (upperStarComp _ φ̄ σY.hom).hom.app P.carrier.X ≫
        (φ̄)^*[_].map (frobeniusStr P) :=
  (frobeniusStr_upperStar_aux φ P).trans (hom_inv_id_app_upperStar_assoc φ _ _ _)

/-- **Pullbacks of compatible pairings are compatible**, in pullback form. -/
theorem upperStar_pairing_frobeniusStr (P Q R : ProEtaleWeilSheaf k₀ l Y)
    (e : P.carrier.X ⊗ Q.carrier.X ⟶ R.carrier.X)
    (h : (frobeniusStr P ⊗ₘ frobeniusStr Q) ≫ e =
      μ (σY.hom)^*[WeilCoefficients.{u} l] _ _ ≫ (σY.hom)^*[_].map e ≫ frobeniusStr R) :
    (frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj P) ⊗ₘ
        frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj Q)) ≫
        (μ (φ̄)^*[WeilCoefficients.{u} l] P.carrier.X Q.carrier.X ≫ (φ̄)^*[_].map e) =
      μ (σX.hom)^*[WeilCoefficients.{u} l] _ _ ≫
        (σX.hom)^*[_].map (μ (φ̄)^*[WeilCoefficients.{u} l] P.carrier.X Q.carrier.X ≫
          (φ̄)^*[_].map e) ≫ frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj R) := by
  set ψ := (upperStarComp (WeilCoefficients.{u} l) σX.hom φ̄).symm ≪≫
    upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
      φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm ≪≫
    upperStarComp _ φ̄ σY.hom
  have hψ : NatTrans.IsMonoidal ψ.hom := by
    simp only [ψ, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have hψt := NatTrans.IsMonoidal.tensor (τ := ψ.hom) P.carrier.X Q.carrier.X
  have nψ := ψ.hom.naturality e
  have hs (S : ProEtaleWeilSheaf k₀ l Y) : frobeniusStr ((ProEtaleWeilSheaf.upperStar k₀ l φ).obj S) =
      ψ.hom.app S.carrier.X ≫ (φ̄)^*[_].map (frobeniusStr S) := by
    rw [frobeniusStr_upperStar]
    simp [ψ]
  simp only [Functor.LaxMonoidal.comp_μ, Functor.comp_map, Functor.comp_obj] at hψt nψ
  rw [hs, hs, hs, ← tensorHom_comp_tensorHom_assoc, μ_natural_assoc, ← Functor.map_comp, h]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hψt, reassoc_of% nψ]

end UpperStar

end ProEtaleWeilSheaf

end AlgebraicGeometry
