/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeCompactification
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedUnitBaseChange
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangePoint

/-! # The bridge (D): the geometric-fibre exchange is the pasted compact-support base change

`descendedShriekGeometricExchange l (toPoint X)` (the exchange consumed by the descended-trace
bridge `geometricFiberWeilSmoothTrace_weilUniversal_of_unitBaseChange`) and
`compactificationLowerShriekBaseChange l bcj` (the pasted base change for which A1' over a point
is proved, `isIso_smoothUnitBaseChange_toPoint`) are isomorphisms between the same functors.
`ExchangeEqPaste` records their equality; it transports invertibility of the exceptional base
change map at the unit from the pasted isomorphism to the geometric-fibre exchange. -/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  (bcj : boundedConstructibleLowerShriek l (structureCompactification X).overI ⋙
      boundedConstructibleUpperStarOfMap l
        (structureCompactification X).overObj.hom.geometricFiberProj ≅
    boundedConstructibleUpperStarOfMap l X.hom.geometricFiberProj ⋙
      boundedConstructibleLowerShriek l (geometricFiberOverMap (structureCompactification X).overI))

/-- The geometric-fibre exchange of the structure morphism is the pasted compact-support base
change of the chosen compactification (statement; the bridge (D)). -/
def ExchangeEqPaste : Prop :=
  (descendedShriekGeometricExchange l (toPoint X)).hom =
    (compactificationLowerShriekBaseChange l bcj).hom

/-- **A1' over a point for the geometric-fibre exchange**: invertibility of the exceptional base
change map at the unit transports from the pasted base change to the geometric-fibre exchange. -/
theorem isIso_smoothUnitBaseChange_descendedShriekGeometricExchange_toPoint
    (hEx : (mateEquiv
        (boundedConstructibleOpenImmersionUpperStarAdjunction l (structureCompactification X).overI)
        (boundedConstructibleOpenImmersionUpperStarAdjunction l
          (geometricFiberOverMap (structureCompactification X).overI)) (inv bcj.hom)).natTrans =
      (upperStarOfMapSquareIso l (structureCompactification X).overI
        (geometricFiberOverMap (structureCompactification X).overI)
        (isPullback_geometricFiberOverMap (structureCompactification X).overI).w).hom)
    (e : (boundedConstructibleUpperStarOfMap l (point k).hom.geometricFiberProj).obj (𝟙_ _) ⟶
      𝟙_ _) [IsIso e] (h : ExchangeEqPaste l bcj) :
    IsIso (smoothUnitBaseChange l (toPoint X) (traceGeometricFiberOverMap (toPoint X))
      (descendedShriekGeometricExchange l (toPoint X)) e) := by
  haveI := isIso_smoothUnitBaseChange_toPoint l bcj hEx e
  change IsIso (Adjunction.unitBaseChange _ _ (descendedShriekGeometricExchange l (toPoint X)).hom e)
  rw [show (descendedShriekGeometricExchange l (toPoint X)).hom =
    (compactificationLowerShriekBaseChange l bcj).hom from h]
  exact this

/-- The geometric-fibre exchange of the structure morphism is the canonical pasted base change
`geometricFiberLowerShriekBaseChangePoint` of #2144 (statement; the bridge (D) in the form
needing no open-immersion input). -/
def ExchangeEqPoint : Prop :=
  (descendedShriekGeometricExchange l (toPoint X)).hom =
    (geometricFiberLowerShriekBaseChangePoint l (toPoint X)).hom

/-- **A1' over a point for the geometric-fibre exchange, from #2144**: invertibility transports
from `geometricFiberLowerShriekBaseChangePoint`. -/
theorem isIso_smoothUnitBaseChange_descendedShriekGeometricExchange_toPoint_of_eqPoint
    (e : (boundedConstructibleUpperStarOfMap l (point k).hom.geometricFiberProj).obj (𝟙_ _) ⟶
      𝟙_ _) [IsIso e] (h : ExchangeEqPoint l (X := X)) :
    IsIso (smoothUnitBaseChange l (toPoint X) (traceGeometricFiberOverMap (toPoint X))
      (descendedShriekGeometricExchange l (toPoint X)) e) := by
  haveI := isIso_smoothUnitBaseChange_geometricFiberLowerShriekBaseChangePoint l (toPoint X) e
  change IsIso (Adjunction.unitBaseChange _ _ (descendedShriekGeometricExchange l (toPoint X)).hom e)
  rw [show (descendedShriekGeometricExchange l (toPoint X)).hom =
    (geometricFiberLowerShriekBaseChangePoint l (toPoint X)).hom from h]
  exact this

end AlgebraicGeometry.ProEtale.CondensedRing
