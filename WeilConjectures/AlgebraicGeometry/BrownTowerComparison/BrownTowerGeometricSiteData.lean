/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerGeometricTransportData
/-! # Site and comparison part of geometric Brown transport -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison
variable {O : Type (u + 1)} [CommRing O] {t : O}
  {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}

/-- The site, compact-support comparison, and bounded unit/counit data occurring
before the common-bound reflection field of geometric transport.
Source: Zheng Construction 4.1, Lemmas 4.10 and 5.22; Stacks 099R and 099W.
(blueprint: lem-route-brown-tower-geometric-transport-core-exists).
-/
structure GeometricTransportSiteData (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S) (H : FiniteEvaluation S G) where
  [finite : ∀ n : ℕ, Finite (Ring O t n)]
  siteX : Site X O t S.PX
  siteY : Site Y O t S.PY
  compact : ProCompact S siteX siteY
  compactComparison : S.functor ⋙ siteY.inverse ⟶ siteX.inverse ⋙ compact.functor
  compactEvaluation : ∀ n,
    compact.functor ⋙ siteY.proEvaluation.evaluation n ⋙ (siteY.realization n).derived ≅
    siteX.proEvaluation.evaluation n ⋙ (siteX.realization n).derived ⋙
      FiniteCoefficientAdjoints.lower (Ring O t n) c
  realizationX : ∀ n, siteX.etaleRealization n = H.realizationX n
  realizationY : ∀ n, siteY.etaleRealization n = H.realizationY n
  compactComparison_evaluation : ∀ n K
      (hK : DerivedCategory.TStructure.t.plus
        ((H.realizationX n).derived.obj ((S.PX.evaluation n).obj K))),
    (siteY.realization n).derived.map
      ((siteY.proEvaluation.evaluation n).map (compactComparison.app K)) ≫
      (compactEvaluation n).hom.app (siteX.inverse.obj K) ≫
      (FiniteCoefficientAdjoints.lower (Ring O t n) c).map
        ((siteX.realization n).derived.map
          ((siteX.comparison.evaluation.inverseEvaluation n).hom.app K) ≫
          (siteX.inverseLevel n).hom.app ((S.PX.evaluation n).obj K)) =
    (siteY.realization n).derived.map
      ((siteY.comparison.evaluation.inverseEvaluation n).hom.app (S.functor.obj K)) ≫
      (siteY.inverseLevel n).hom.app ((S.PY.evaluation n).obj (S.functor.obj K)) ≫
      (FiniteCoefficientAdjoints.nu (Ring O t n) Y).map
        (eqToHom (congrArg
          (fun R ↦ R.derived.obj ((S.PY.evaluation n).obj (S.functor.obj K)))
          (realizationY n)) ≫
        (H.realizationY n).derived.map ((S.evaluation n).hom.app K) ≫
          (H.lower n).hom.app ((S.PX.evaluation n).obj K)) ≫
      (ProEtale.compactSupportSiteComparison (Ring O t n) c).inv.app
        ⟨(H.realizationX n).derived.obj ((S.PX.evaluation n).obj K), hK⟩ ≫
      (FiniteCoefficientAdjoints.lower (Ring O t n) c).map
        ((FiniteCoefficientAdjoints.nu (Ring O t n) X).map
          (eqToHom (congrArg
            (fun R ↦ R.derived.obj ((S.PX.evaluation n).obj K))
            (realizationX n).symm)))
  compact_iso : ∀ K, (∃ a : ℤ, K.IsGE a) → IsIso (compactComparison.app K)
  unit_iso_X : ∀ K, (∃ a : ℤ, K.IsGE a) → IsIso (siteX.adjunction.unit.app K)
  unit_iso_Y : ∀ K, (∃ a : ℤ, K.IsGE a) → IsIso (siteY.adjunction.unit.app K)
  counit_iso_X : ∀ K, siteX.Origin K → IsIso (siteX.adjunction.counit.app K)
  counit_iso_Y : ∀ K, siteY.Origin K → IsIso (siteY.adjunction.counit.app K)

/-- Site and comparison data are supplied by the geometric finite-level and
pro-etale comparison constructions. The proof is the construction in Zheng
Construction 4.1 and Lemmas 4.10 and 5.22: form ordinary and universal derived
images at X, Z, and Y, then paste the proper/open mates. Finite site full
faithfulness gives the unit and counit assertions, and levelwise evaluation
identifies the displayed comparison equation. -/
theorem geometricTransportSiteData_exists
    (S : StrictEtaleCompactSupport O t c)
    (G : EtaleTowerBrownAdjunction S)
    (H : FiniteEvaluation S G) :
    Nonempty (GeometricTransportSiteData S G H) := by
  sorry

end BrownTowerComparison
end AlgebraicGeometry
