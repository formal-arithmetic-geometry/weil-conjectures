module

public import WeilConjectures.Scratch.T3

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

section Counit

variable {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : X ⟶ Y) [φ.IsOver (Spec (CommRingCat.of k₀))] [QuasiCompact φ] [QuasiSeparated φ]
  [LocallyOfFiniteType φ] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  {F : WeilSheaf k₀ l X}

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

set_option profiler true in
/-- For a morphism `c : G ⟶ φ̄_* F` of the underlying sheaves compatible with the Weil
structures of `G` and `φ_* F`, the composite `φ̄^* G ⟶ φ̄^* φ̄_* F ⟶ F` of `φ̄^* c` with the
counit is compatible with the Weil structures. -/
lemma map_comp_lowerStar_counit_frobeniusStr_compatible {G : WeilSheaf k₀ l Y}
    (c : G.obj.carrier.X ⟶ (φ̄)_*[WeilCoefficients.{u} l].obj F.obj.carrier.X)
    (hc : ((Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[_].map c ≫
      ((lowerStar φ).obj F).frobeniusStr = G.frobeniusStr ≫ c) :
    (ProEtale.upperStarComp _ (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom
      (φ̄)).hom.app G.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom)^*[_].map
          ((φ̄)^*[_].map c ≫
            (ProEtale.upperStarLowerStarAdjunction _ (φ̄)).counit.app F.obj.carrier.X) ≫
        F.frobeniusStr =
      (ProEtale.upperStarCongr _ (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
          φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.app G.obj.carrier.X ≫
        (ProEtale.upperStarComp _ (φ̄)
          (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).hom.app G.obj.carrier.X ≫
        (φ̄)^*[_].map G.frobeniusStr ≫ (φ̄)^*[_].map c ≫
        (ProEtale.upperStarLowerStarAdjunction _ (φ̄)).counit.app F.obj.carrier.X := by
  have n₁ := (ProEtale.upperStarComp (WeilCoefficients.{u} l)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom (φ̄)).hom.naturality c
  have n₂ := (ProEtale.upperStarCongr (WeilCoefficients.{u} l)
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius
      φ (comp_over φ (Spec (CommRingCat.of k₀)))).symm).hom.naturality c
  have n₃ := (ProEtale.upperStarComp (WeilCoefficients.{u} l) (φ̄)
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.hom).hom.naturality c
  simp only [Functor.comp_map] at n₁ n₂ n₃
  rw [Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% n₁.symm, lowerStar_counit_frobeniusStr_compatible, reassoc_of% n₂,
    reassoc_of% n₃, ← Functor.map_comp_assoc, hc, Functor.map_comp_assoc]

end Counit

end AlgebraicGeometry.WeilSheaf
