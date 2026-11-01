/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerivedLinear
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Explicit cycle representatives in a normalized mapping model

Source: Stacks 09L9 and 070I.
(blueprint: lem-sf-derived-mapping-cohomology-cycles)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe b v u w

open CategoryTheory Opposite CochainComplex.HomComplex

namespace CategoryTheory.DerivedMappingAction

variable {B : Type b} [CommRing B]
  [HasDerivedCategory.{max b v} (ModuleCat.{max b v} (ULift.{v} B))]
  {A : Type u} [Category.{v} A] [Abelian A] [Linear B A]
  [HasDerivedCategory.{w} A]

/-- A cycle of the model is a cocycle of the explicit cochain differential.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-cohomology-cycles).
Proof: apply the degree identification to the equation iCycles followed by d equals zero. -/
theorem HomModel.cycle_differential (S : HomModel (B := B) A)
    (X Y : CochainComplex A ℤ) (n : ℤ) (x : (S.ordinary.obj (op X, Y)).cycles n) :
    δ n (n + 1) (((S.degree X Y n).hom
      ((S.ordinary.obj (op X, Y)).iCycles n x)).down) = 0 := by
  rw [← S.differential]
  have hx : (S.ordinary.obj (op X, Y)).d n (n + 1)
      ((S.ordinary.obj (op X, Y)).iCycles n x) = 0 := by
    change ((S.ordinary.obj (op X, Y)).iCycles n ≫
      (S.ordinary.obj (op X, Y)).d n (n + 1)) x = 0
    rw [HomologicalComplex.iCycles_d]
    rfl
  rw [hx]
  simp

/-- The actual cochain cocycle underlying a cycle in the model.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-cohomology-cycles). -/
def HomModel.cycleCocycle (S : HomModel (B := B) A) (X Y : CochainComplex A ℤ)
    (n : ℤ) (x : (S.ordinary.obj (op X, Y)).cycles n) : Cocycle X Y n :=
  ⟨((S.degree X Y n).hom ((S.ordinary.obj (op X, Y)).iCycles n x)).down,
    (Cocycle.mem_iff n (n + 1) rfl _).mpr (S.cycle_differential X Y n x)⟩

/-- The actual map into a shift represented by a model cycle.
Source: Stacks 09L9 (blueprint: lem-sf-derived-mapping-cohomology-cycles). -/
def HomModel.cycleToMap (S : HomModel (B := B) A) (X Y : CochainComplex A ℤ)
    (n : ℤ) (x : (S.ordinary.obj (op X, Y)).cycles n) : X ⟶ Y⟦n⟧ :=
  Cocycle.equivHomShift.symm (S.cycleCocycle X Y n x)

end CategoryTheory.DerivedMappingAction
