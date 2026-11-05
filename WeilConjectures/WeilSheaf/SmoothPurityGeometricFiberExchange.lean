/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityFieldCompactificationExchange
public import WeilConjectures.WeilSheaf.SmoothPurityOpenFieldBaseChange
public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeComp
public import WeilConjectures.WeilSheaf.SmoothPurityChartBaseChange

/-! # One geometric-fiber exchange for all compact-support morphisms

Use the geometric fiber of the chosen compactification and restrict the ambient exchange.
For open immersions the exceptional mate is invertible at every object, independently of
normalization, by full faithfulness. Composition compatibility is a separate obligation.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing
open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [PerfectField k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  [Fact (ringChar (AlgebraicClosure k)).Prime]
  [Fact (ringChar (AlgebraicClosure k) ≠ ℓ)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The geometric-fiber compact-support exchange, uniformly for every morphism over `k`. -/
def purityGeometricFiberLowerShriekExchange :
    boundedConstructibleLowerShriek ℓ f ⋙
        boundedConstructibleUpperStarOfMap ℓ (purityGeometricFiberProj Y) ≅
      boundedConstructibleUpperStarOfMap ℓ (purityGeometricFiberProj X) ⋙
        boundedConstructibleLowerShriek ℓ ((purityGeometricFiber k).map f) := by
  let c := compactificationOverField f
  have : WeaklyEtale (c.g ≫ Y.hom).geometricFiberProj := by
    exact inferInstanceAs (WeaklyEtale (purityGeometricFiberProj (Over.mk (c.g ≫ Y.hom))))
  exact purityFieldLowerShriekExchange ℓ f ((purityGeometricFiber k).map f)
    c (c.geometricFiber (Over.w f))
    (Scheme.Hom.isPullback_geometricFiberMap c.i (c.i_comp_g_comp (Over.w f)))
    (Scheme.Hom.isPullback_geometricFiberMap c.g rfl).flip


/-- The exceptional mate of the global geometric-fiber exchange for an open immersion. -/
theorem isIso_purityGeometricFiberLowerShriekExchange_mate_of_isOpenImmersion
    [IsOpenImmersion f.left] (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((upperShriekMateOfMap ℓ f ((purityGeometricFiber k).map f)
      (purityGeometricFiberLowerShriekExchange ℓ f)).app N) := by
  simpa only [upperShriekMateOfMap, IsIso.Iso.inv_hom] using
    isIso_smoothExceptionalMate_of_isOpenImmersion ℓ f ((purityGeometricFiber k).map f)
    (purityGeometricFiber_isPullback f).toCommSq
    (purityGeometricFiberLowerShriekExchange ℓ f) N

/-- The open unit case for the same global exchange. -/
theorem isIso_smoothUnitBaseChange_purityGeometricFiberExchange_of_isOpenImmersion
    [IsOpenImmersion f.left]
    (e : (boundedConstructibleUpperStarOfMap ℓ (purityGeometricFiberProj Y)).obj (𝟙_ _) ⟶ 𝟙_ _)
    [IsIso e] :
    IsIso (smoothUnitBaseChange ℓ f ((purityGeometricFiber k).map f)
      (purityGeometricFiberLowerShriekExchange ℓ f) e) :=
  isIso_smoothUnitBaseChange_of_isOpenImmersion ℓ f ((purityGeometricFiber k).map f)
    (purityGeometricFiber_isPullback f).toCommSq _ e

end AlgebraicGeometry.ProEtale.CondensedRing
