/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldPastedIsIso
public import WeilConjectures.WeilSheaf.SmoothPurityDescendedUnitBaseChange
public import WeilConjectures.WeilSheaf.SmoothPurityRelativeUnitIso

/-! # Invertibility for the actual descended exchange over an arbitrary base -/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (l : ℕ) [Fact l.Prime] {k : Type u} [Field k] [Finite k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The unit mate of the exact exchange used by finite-base descent is invertible
for an arbitrary relative morphism. The two factors use the chosen compactification itself
and its geometric fibre. -/
theorem isIso_smoothUnitBaseChange_descendedShriekGeometricExchange_relative
    (e : (boundedConstructibleUpperStarOfMap l (X := Y)
      (Y := geometricFiberOver Y) Y.hom.geometricFiberProj).obj
        (𝟙_ _) ⟶ 𝟙_ _) [IsIso e] :
    IsIso (smoothUnitBaseChange l f (traceGeometricFiberOverMap f)
      (descendedShriekGeometricExchange l f) e) := by
  have hp : IsIso ((upperShriekBaseChangeOfMap l
      (f := (compactificationOverField f).overG (f := f))
      (f' := ((compactificationOverField f).geometricFiber (Over.w f)).overG
        (f := traceGeometricFiberOverMap f))
      (Scheme.Hom.isPullback_geometricFiberMap (g := Y.hom)
        (compactificationOverField f).g rfl).flip).app (𝟙_ _)) := by
    simpa only [geometricFiberOver, geometricFiberOverMap, traceGeometricFiberOverMap,
      Compactification.overObj, Compactification.overG, Compactification.geometricFiber_g,
      Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure] using
      purity_isIso_upperShriekBaseChangeOfMap_unit_geometricFiber l
        ((compactificationOverField f).overG (f := f))
  dsimp only [descendedShriekGeometricExchange]
  exact isIso_smoothUnitBaseChange_fieldCompactification_of_proper l f
    (traceGeometricFiberOverMap f)
    (compactificationOverField f) ((compactificationOverField f).geometricFiber (Over.w f))
    (Scheme.Hom.isPullback_geometricFiberMap (compactificationOverField f).i
      ((compactificationOverField f).i_comp_g_comp (Over.w f)))
    (Scheme.Hom.isPullback_geometricFiberMap (g := Y.hom)
      (compactificationOverField f).g rfl).flip e

/-- The descended smooth trace is universal over an arbitrary base for the specified
geometric compactification, without an additional base-change hypothesis. -/
theorem geometricFiberWeilSmoothTrace_weilUniversal_relative
    (e : (boundedConstructibleUpperStarOfMap l (X := Y)
      (Y := geometricFiberOver Y) Y.hom.geometricFiberProj).obj
        (𝟙_ _) ≅ 𝟙_ _)
    (d : ℕ) [SmoothOfRelativeDimension d f.left]
    (K : DerivedCategory (Endofunctor.IsoAlgebra
      (lowerStar (Profinite.padicAlgClRingObj l) X.hom.geometricGaloisFrobenius.inv)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj l)
      X.hom.geometricFiber) ((Endofunctor.IsoAlgebra.forget _).mapDerivedCategory.obj K)) :
    (weilRightDerivedLowerShriek (Profinite.padicAlgClRingObj l)
      (compactificationOverField f) (Over.w f)).TraceUniversalAt K
        (geometricFiberWeilSmoothTrace l f d) := by
  have := isIso_smoothUnitBaseChange_descendedShriekGeometricExchange_relative l f e.hom
  exact geometricFiberWeilSmoothTrace_weilUniversal_of_unitBaseChange l f e d K hK

end AlgebraicGeometry.ProEtale.CondensedRing
