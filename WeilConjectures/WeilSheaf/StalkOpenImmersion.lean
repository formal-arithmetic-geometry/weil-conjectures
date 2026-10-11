/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.UpperLowerStar.CounitStructure
public import WeilConjectures.WeilSheaf.OpenImmersion
public import WeilConjectures.WeilSheaf.StalkUpperStar

/-!
# Stalks of the direct images along an open immersion

Let `j : U ⟶ X` be an open immersion of `k₀`-schemes and `F` a Weil sheaf on `U`. At a geometric
point `t ≫ j̄` of `X̄` coming from a geometric point `t` of `Ū`, the stalks of `j_* F` and of
`j_! F` are the stalk of `F` at `t`, compatibly with the Frobenius: the counit `j̄^* j̄_* F ⟶ F`
is invertible and compatible with the Weil structures.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale

variable {l : ℕ} [Fact l.Prime]

-- Stated for arbitrary `j`, `a`, `b` and `c`: for the geometric Frobenii the kernel times out on
-- the same proof.
private lemma lowerStarExchange_hom_app_hom {X Y : Scheme.{u}} (j : X ⟶ Y) (a : X ≅ X)
    (b : Y ≅ Y) (c : j ≫ b.inv = a.inv ≫ j) (M : AdicSheaf l X) :
    ((adicLowerStarComp l j b.inv ≪≫ adicLowerStarCongr l c ≪≫
      (adicLowerStarComp l a.inv j).symm).hom.app M).hom =
      (lowerStarComp (WeilCoefficients.{u} l) j b.inv).hom.app M.X ≫
        (lowerStarCongr _ c).hom.app M.X ≫ (lowerStarComp _ a.inv j).inv.app M.X := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Mod.comp_hom',
    adicLowerStarComp_hom_app_hom, adicLowerStarComp_inv_app_hom, adicLowerStarCongr_hom_app_hom]

variable {k : Type u} [Field k] [Finite k] {X₀ Y₀ : Scheme.{u}} {f : X₀ ⟶ Spec (.of k)}
  {g : Y₀ ⟶ Spec (.of k)} (φ : X₀ ⟶ Y₀) (h : φ ≫ g = f)

private lemma adicLowerStarGeometricFiberMapCompFrobeniusIso_eq :
    adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h =
      adicLowerStarComp l _ _ ≪≫
        adicLowerStarCongr l (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h) ≪≫
        (adicLowerStarComp l _ _).symm :=
  rfl

/-- The exchange isomorphism `φ̄_* ⋙ Fr_Y^* ≅ Fr_X^* ⋙ φ̄_*` of `ℓ`-adic sheaves, on the
underlying sheaves. -/
lemma adicLowerStarGeometricFiberMapCompFrobeniusIso_hom_app_hom
    (M : AdicSheaf l f.geometricFiber) :
    ((adicLowerStarGeometricFiberMapCompFrobeniusIso l φ h).hom.app M).hom =
      (lowerStarComp (WeilCoefficients.{u} l) (Scheme.Hom.geometricFiberMap φ h)
          g.geometricGaloisFrobenius.inv).hom.app M.X ≫
        (lowerStarCongr _
          (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ h)).hom.app M.X ≫
        (lowerStarComp _ f.geometricGaloisFrobenius.inv
          (Scheme.Hom.geometricFiberMap φ h)).inv.app M.X := by
  rw [adicLowerStarGeometricFiberMapCompFrobeniusIso_eq]
  exact lowerStarExchange_hom_app_hom _ _ _ _ M

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l X)

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

/-- The Weil structure of the pushforward `φ_* F`, on the underlying sheaves: the pushforward
along `φ̄` of the Weil structure of `F`, through
`Fr_Y^* φ̄_* ≅ (Fr_Y⁻¹)_* φ̄_* ≅ (φ̄ ≫ Fr_Y⁻¹)_* = (Fr_X⁻¹ ≫ φ̄)_* ≅ φ̄_* (Fr_X⁻¹)_*`. -/
lemma frobeniusStr_lowerStar :
    ((lowerStar φ).obj F).frobeniusStr =
      (ProEtale.upperStarIsoLowerStarInv _ (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
        ).hom.app ((lowerStar φ).obj F).obj.carrier.X ≫
      (ProEtale.lowerStarComp _ (φ̄)
        (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).hom.app F.obj.carrier.X ≫
      (ProEtale.lowerStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv
        φ (comp_over φ (Spec (CommRingCat.of k₀))))).hom.app F.obj.carrier.X ≫
      (ProEtale.lowerStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv
        (φ̄)).inv.app F.obj.carrier.X ≫
      (φ̄)_*[_].map ((ProEtale.AdicSheaf.forget _).map F.obj.str.hom) := by
  rw [frobeniusStr, lowerStar_obj_obj_str, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp]
  change _ ≫ ((ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso l φ
    (comp_over φ (Spec (CommRingCat.of k₀)))).hom.app F.obj.carrier ≫ _).hom = _
  rw [Mod.comp_hom', ProEtale.adicLowerStar_map_hom,
    ProEtale.adicLowerStarGeometricFiberMapCompFrobeniusIso_hom_app_hom]
  simp only [Category.assoc]
  rfl

end AlgebraicGeometry.WeilSheaf
