/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeProper
public import WeilConjectures.WeilSheaf.SmoothPurityFullyFaithfulBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedComplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DualizingFieldChange.GenericPoint

/-! # Cross-field proper mates and the open Step 2 interface

All-object versions of the proper coordinate transport and K9's open mate criterion.
-/

set_option profiler true
set_option profiler.threshold 0

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k₁ k₂ : Type u} [Field k₁] [Field k₂]
  [Fact (ringChar k₁).Prime] [Fact (ringChar k₁ ≠ ℓ)]
  [Fact (ringChar k₂).Prime] [Fact (ringChar k₂ ≠ ℓ)]
  {X Y : Over (Spec (.of k₁))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Over (Spec (.of k₂))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  (f : X ⟶ Y) (f' : X' ⟶ Y')
  {πX : X'.left ⟶ X.left} {πY : Y'.left ⟶ Y.left}


/-- The proper compact-support exchange has the standard proper exceptional mate at every object. -/
lemma purity_properLowerShriekBaseChange_mate_app
    [IsProper f.left] [IsProper f'.left]
    (sq : IsPullback πX f'.left f.left πY)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (upperShriekMateOfMap ℓ f f' (properLowerShriekBaseChangeOfMap ℓ f f' sq)).app N =
      (upperShriekBaseChangeOfMap ℓ sq).app N := by
  have := isIso_boundedConstructibleBaseChangeOfMap ℓ sq
  have h := Adjunction.unitBaseChange_ofNatIsoLeft
    (boundedConstructibleUpperShriekAdjunction ℓ f)
    (boundedConstructibleUpperShriekAdjunction ℓ f')
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f)
    (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f')
    (boundedConstructibleBaseChangeOfMap ℓ sq.toCommSq)
    (𝟙 ((boundedConstructibleUpperStarOfMap ℓ πY).obj N))
  simpa only [Adjunction.unitBaseChange, Functor.map_id, Category.comp_id] using h

/-- The proper smooth exceptional mate is invertible at all bounded constructible objects. -/
theorem isIso_purityProperMate_of_smooth
    [IsProper f.left] [IsProper f'.left] [WeaklyEtale πY]
    (sq : IsPullback πX f'.left f.left πY) (d : ℕ)
    [SmoothOfRelativeDimension d f.left]
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((upperShriekMateOfMap ℓ f f'
      (properLowerShriekBaseChangeOfMap ℓ f f' sq)).app N) := by
  rw [purity_properLowerShriekBaseChange_mate_app]
  exact isIso_upperShriekBaseChangeOfMap_app_of_smooth_of_weaklyEtale ℓ d sq N

/-- The closed-immersion exceptional mate is invertible at all bounded constructible objects. -/
theorem isIso_purityProperMate_of_isClosedImmersion
    [IsClosedImmersion f.left] [IsClosedImmersion f'.left] [WeaklyEtale πY]
    (sq : IsPullback πX f'.left f.left πY)
    (N : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    IsIso ((upperShriekMateOfMap ℓ f f'
      (properLowerShriekBaseChangeOfMap ℓ f f' sq)).app N) := by
  rw [purity_properLowerShriekBaseChange_mate_app]
  exact isIso_upperShriekBaseChangeOfMap_app_of_weaklyEtale ℓ sq N

end AlgebraicGeometry.ProEtale.CondensedRing
