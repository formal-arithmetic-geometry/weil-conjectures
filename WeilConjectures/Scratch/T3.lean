module

public import WeilConjectures.WeilSheaf.StalkOpenImmersion
public import WeilConjectures.WeilSheaf.ExtensionByZero

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section FrobeniusStr

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

lemma map_comp_frobeniusStr {F G : WeilSheaf k₀ l X} (α : F ⟶ G) :
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[_].map
        ((ProEtale.AdicSheaf.forget _).map α.hom.hom.f) ≫ G.frobeniusStr =
      F.frobeniusStr ≫ (ProEtale.AdicSheaf.forget _).map α.hom.hom.f := by
  have h := congrArg (ProEtale.AdicSheaf.forget _).map α.hom.hom.h
  rw [Functor.map_comp, Functor.map_comp] at h
  simp only [frobeniusStr, Category.assoc]
  erw [(ProEtale.upperStarIsoLowerStarInv (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius).hom.naturality_assoc]
  exact congrArg (_ ≫ ·) h

end FrobeniusStr

section Counit

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  (F : WeilSheaf k₀ l X)

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

lemma lowerStar_counit_frobeniusStr_compatible :
    (ProEtale.upperStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
      (φ̄)).hom.app ((φ̄)_*[WeilCoefficients.{u} l].obj F.obj.carrier.X) ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[_].map
          ((ProEtale.upperStarLowerStarAdjunction _ (φ̄)).counit.app F.obj.carrier.X) ≫
        F.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app
          ((φ̄)_*[WeilCoefficients.{u} l].obj F.obj.carrier.X) ≫
        (ProEtale.upperStarComp _ (φ̄)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).hom.app
          ((φ̄)_*[WeilCoefficients.{u} l].obj F.obj.carrier.X) ≫
        (φ̄)^*[_].map ((lowerStar φ).obj F).frobeniusStr ≫
        (ProEtale.upperStarLowerStarAdjunction _ (φ̄)).counit.app F.obj.carrier.X := by
  rw [frobeniusStr_lowerStar, frobeniusStr]
  have key := ProEtale.upperStarComp_hom_app_comp_map_counit_comp_structure' (WeilCoefficients.{u} l) (φ̄)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ (comp_over φ (Spec (CommRingCat.of k₀))))
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ (comp_over φ (Spec (CommRingCat.of k₀)))) F.obj.carrier.X
    ((ProEtale.AdicSheaf.forget _).map F.obj.str.hom)
  exact key

end Counit

end AlgebraicGeometry.WeilSheaf
