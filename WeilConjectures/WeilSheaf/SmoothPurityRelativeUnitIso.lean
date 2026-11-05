module

public import WeilConjectures.WeilSheaf.SmoothPurityRelativeUnitDual
public import WeilConjectures.WeilSheaf.SmoothPurityPointDualizingIso

/-! Relative exceptional unit base change from absolute Verdier duality. -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- An isomorphism of relative exceptional units across the geometric fibre, constructed
from biduality, the projection formula, and point base change on both schemes. -/
def purityGeometricFiberUpperShriekUnitIso :
    (boundedConstructibleUpperStarOfMap l (X := X) (Y := geometricFiberOver X)
        X.hom.geometricFiberProj).obj ((boundedConstructibleUpperShriek l f).obj (𝟙_ _)) ≅
      (boundedConstructibleUpperShriek l (geometricFiberOverMap f)).obj (𝟙_ _) := by
  let F := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l f
  let F' := boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l
    (geometricFiberOverMap f)
  let G := boundedConstructibleUpperStarOfMap l (X := X) (Y := geometricFiberOver X)
    X.hom.geometricFiberProj
  let H := boundedConstructibleUpperStarOfMap l (X := Y) (Y := geometricFiberOver Y)
    Y.hom.geometricFiberProj
  let K := F.obj (dualizingComplex l Y)
  have hc := isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale l
    (P := X) (P' := geometricFiberOver X) X.hom.geometricFiberProj
    (dualizingComplex l X) K
  rw [Verdier.nearbyDualityMap_id_eq_ihomComparison] at hc
  let e : G.obj K ≅ F'.obj (dualizingComplex l (geometricFiberOver Y)) :=
    (boundedConstructibleUpperStarCompUpperStarOfMapIso l f (geometricFiberOverMap f)
      (isPullback_geometricFiberOverMap f).w).app (dualizingComplex l Y) ≪≫
      F'.mapIso (purityGeometricFiberDualizingIso l Y)
  exact G.mapIso (purityUpperShriekUnitDualIso l f) ≪≫
    asIso ((Functor.LaxMonoidal.ihomComparison G K).natTrans.app (dualizingComplex l X)) ≪≫
    (ihom (G.obj K)).mapIso (purityGeometricFiberDualizingIso l X) ≪≫
    ihomIsoOfIsoLeft e (dualizingComplex l (geometricFiberOver X)) ≪≫
    (purityUpperShriekUnitDualIso l (geometricFiberOverMap f)).symm

/-- For a proper relative morphism the specified exceptional base change at the unit is
invertible. An abstract Verdier-duality isomorphism suffices by the endomorphism criterion. -/
theorem purity_isIso_upperShriekBaseChangeOfMap_unit_geometricFiber [IsProper f.left] :
    IsIso ((upperShriekBaseChangeOfMap l (isPullback_geometricFiberOverMap f)).app (𝟙_ _)) := by
  have h := isIso_nearbyDualityMap_upperStarOfMap_id_of_weaklyEtale l
    (P := Y) (P' := geometricFiberOver Y) Y.hom.geometricFiberProj (𝟙_ _)
    ((boundedConstructibleLowerStar l f).obj (𝟙_ _))
  have := isIso_lowerStar_map_upperShriekBaseChangeOfMap_app l
    (isPullback_geometricFiberOverMap f) (𝟙_ _) h
  let e := Functor.Monoidal.εIso (boundedConstructibleUpperStarOfMap l
    (X := Y) (Y := geometricFiberOver Y) Y.hom.geometricFiberProj)
  exact isIso_upperShriekBaseChangeOfMap_app_of_iso l (isPullback_geometricFiberOverMap f)
    (𝟙_ _) (purityGeometricFiberUpperShriekUnitIso l f ≪≫
      (boundedConstructibleUpperShriek l (geometricFiberOverMap f)).mapIso e)

end AlgebraicGeometry.ProEtale.CondensedRing
