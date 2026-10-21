/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q135
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.Functor

/-!
# Strict derived-limit data and diagram postcomposition

Source: Stacks Project, Cohomology on Sites, Tags 0940 and 0941,
section-derived-limits and lemma-derived-limit-is-ok
(blueprint: def-weil-pbc-strict-projection-limit-data).

`StrictProjectionLimitData` names the total right derived limit, its ordinary comparison,
K-injective computation, derived evaluation and natural Roos triangle. For sheaves of modules
these are precisely the data in lem-weil-pbc-ringed-strict-tower-homotopy-limit. This record
only packages supplied data; it does not choose a functor or assert existence for an arbitrary
abelian category. `projectionPost` is ordinary diagram postcomposition.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe uI vI uB vB uD vD uDB vDB uDT vDT
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

namespace SheafOfModules

/-- Postcomposition on diagrams, retaining the original functor and natural transformations.
Source: Stacks 0940 (blueprint: def-weil-pbc-strict-projection-limit-data). -/
def projectionPost {I : Type uI} {B : Type uB} {D : Type uD}
    [Category.{vI} I] [Category.{vB} B] [Category.{vD} D] (F : B ⥤ D) : (I ⥤ B) ⥤ (I ⥤ D) :=
  (Functor.whiskeringRight I B D).obj F

/-- Postcomposition by an additive functor is additive, via Mathlib's whiskering instance.
Source: Stacks 0940 (blueprint: def-weil-pbc-strict-projection-limit-data). -/
instance projectionPost_additive {I : Type uI} {B : Type uB} {D : Type uD}
    [Category.{vI} I] [Category.{vB} B] [Category.{vD} D]
    [Preadditive B] [Preadditive D] (F : B ⥤ D) [F.Additive] :
    (projectionPost (I := I) F).Additive :=
  inferInstanceAs (((Functor.whiskeringRight I B D).obj F).Additive)

/-- Preserve Mathlib's zero-map instance for the same diagram postcomposition functor.
Source: Stacks 0940 (blueprint: def-weil-pbc-strict-projection-limit-data). -/
instance projectionPost_preservesZeroMorphisms {I : Type uI} {B : Type uB} {D : Type uD}
    [Category.{vI} I] [Category.{vB} B] [Category.{vD} D]
    [HasZeroMorphisms B] [HasZeroMorphisms D] (F : B ⥤ D)
    [((Functor.whiskeringRight I B D).obj F).PreservesZeroMorphisms] :
    (projectionPost (I := I) F).PreservesZeroMorphisms :=
  inferInstanceAs (((Functor.whiskeringRight I B D).obj F).PreservesZeroMorphisms)

/-- The derived limit, evaluation, and Roos data for an abelian category of strict towers.
For module sheaves this packages the functor, unit, K-injective computation, evaluation,
and natural Roos arrows supplied by `ringedStrictTowerHomotopyLimitIndependentCoefficients`
(lem-weil-pbc-ringed-strict-tower-homotopy-limit). It asserts no existence for arbitrary B.
Source: Stacks 0A07, 0940, 0941
(blueprint: def-weil-pbc-strict-projection-limit-data). -/
structure StrictProjectionLimitData (B : Type uB) [Category.{vB} B] [Abelian B]
    [HasLimitsOfShape ℕᵒᵖ B]
    {DB : Type uDB} {DT : Type uDT} [Category.{vDB} DB] [Category.{vDT} DT]
    [HasZeroObject DB] [HasShift DB ℤ] [Preadditive DB]
    [∀ n : ℤ, (shiftFunctor DB n).Additive] [Pretriangulated DB]
    [HasCountableProducts DB]
    (Q : CochainComplex B ℤ ⥤ DB) (QT : CochainComplex (ℕᵒᵖ ⥤ B) ℤ ⥤ DT)
    [QT.IsLocalization (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (.up ℤ))] where
  L : DT ⥤ DB
  eta : (lim : (ℕᵒᵖ ⥤ B) ⥤ B).mapHomologicalComplex
    (ComplexShape.up ℤ) ⋙ Q ⟶ QT ⋙ L
  ev : DT ⥤ (ℕᵒᵖ ⥤ DB)
  evaluation : QT ⋙ ev ≅
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙ projectionPost Q
  p : ∀ Z, L.obj Z ⟶ ∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)
  delta : ∀ Z, (∏ᶜ fun n : ℕ ↦ (ev.obj Z).obj (op n)) ⟶ (L.obj Z)⟦(1 : ℤ)⟧
  derived : L.IsRightDerivedFunctor eta
    (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ B) (ComplexShape.up ℤ))
  computes : ∀ I : CochainComplex (ℕᵒᵖ ⥤ B) ℤ, I.IsKInjective → IsIso (eta.app I)
  roos : ∀ Z, IsDerivedLimitTriangle
    (fun n : ℕ ↦ (ev.obj Z).map (homOfLE (Nat.le_succ n)).op) (L.obj Z) (p Z) (delta Z)
  p_natural : ∀ {Z W} (v : Z ⟶ W),
    L.map v ≫ p W = p Z ≫ Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n))
  delta_natural : ∀ {Z W} (v : Z ⟶ W),
    Limits.Pi.map (fun n : ℕ ↦ (ev.map v).app (op n)) ≫ delta W =
      delta Z ≫ (L.map v)⟦(1 : ℤ)⟧'

end SheafOfModules
