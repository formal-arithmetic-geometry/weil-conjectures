module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangePoint

/-! The point theorem transports the absolute dualizing object of every scheme. -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]

/-- The pullback of the absolute dualizing object is isomorphic to the absolute
dualizing object on the geometric fibre; no properness or smoothness is assumed. -/
def purityGeometricFiberDualizingIso (X : Over (Spec (.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] :
    (boundedConstructibleUpperStarOfMap l (X := X) (Y := geometricFiberOver X)
        X.hom.geometricFiberProj).obj (dualizingComplex l X) ≅
      dualizingComplex l (geometricFiberOver X) := by
  let e := (Functor.Monoidal.εIso (boundedConstructibleUpperStarOfMap l (X := point k)
    (Y := geometricFiberOver (point k)) (point k).hom.geometricFiberProj)).symm
  have := isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangePoint l (toPoint X) e.hom
  have : IsIso (toPoint (geometricFiberOver (point k))).left := by
    rw [toPoint_left]
    infer_instance
  exact asIso (smoothUnitBaseChange l (toPoint X) (geometricFiberOverMap (toPoint X))
      (geometricFiberLowerShriekBaseChangePoint l (toPoint X)) e.hom) ≪≫
    (boundedConstructibleUpperShriek l (geometricFiberOverMap (toPoint X))).mapIso
      (boundedConstructibleUpperShriekUnitIso_padicAlgCl l
        (toPoint (geometricFiberOver (point k)))).symm ≪≫
    upperShriekDualizingComplexIso l (geometricFiberOverMap (toPoint X))

end AlgebraicGeometry.ProEtale.CondensedRing
