module

public import WeilConjectures.WeilSheaf.StalkOpenImmersion
public import WeilConjectures.WeilSheaf.ExtensionByZero

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
  (F : WeilSheaf k₀ l X)

set_option hygiene false in
local notation "φ̄" => Scheme.Hom.geometricFiberMap φ (comp_over φ (Spec (CommRingCat.of k₀)))

set_option profiler true in
example : True := by
  have key := ProEtale.upperStarComp_hom_app_comp_map_counit_comp_structure' (WeilCoefficients.{u} l) (φ̄)
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    (Y ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius φ (comp_over φ (Spec (CommRingCat.of k₀))))
    (Scheme.Hom.geometricFiberMap_comp_geometricGaloisFrobenius_inv φ (comp_over φ (Spec (CommRingCat.of k₀)))) F.obj.carrier.X
    ((ProEtale.AdicSheaf.forget _).map F.obj.str.hom)
  trivial

end Counit

end AlgebraicGeometry.WeilSheaf
