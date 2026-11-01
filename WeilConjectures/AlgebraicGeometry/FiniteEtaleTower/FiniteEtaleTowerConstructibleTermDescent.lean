/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import Mathlib.FieldTheory.Separable
import WeilConjectures.FieldTheory.TensorProductDiagonal
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement

/-! # Finite-term descent data for the finite etale tower

This isolates the termwise part of the constructible object descent argument.  The
finite-term flat-model and constructibility descent is the Stacks 03TT/09YU argument;
the subsequent differential and finite-Tor assembly is recorded separately.
(blueprint: lem-sf-finite-etale-tower-constructible-term-descent)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.FiniteEtaleTower

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of k))
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

local instance towerMonObj (V : Scheme.{u}) :
    MonObj (condensedRingObj (Profinite.continuousCoefficientRingObj A) V) :=
  Functor.monObjObj (F := upperStarFromPoint V) _

abbrev towerModule (V : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousCoefficientRingObj A) V)

abbrev towerComplex (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (V : Scheme.{u}) :=
  CochainComplex (towerModule (A := A) V) ℤ

structure TermStageData (K : towerComplex A (limitScheme (L := L) y)) where
  model : towerComplex A (limitScheme (L := L) y)
  modelIso : Nonempty ((_root_.DerivedCategory.Q).obj model ≅
    (_root_.DerivedCategory.Q).obj K)
  modelProperty : constantModelBoundedConstructible
      (Profinite.continuousCoefficientRingObj A) (limitScheme (L := L) y)
      ((_root_.DerivedCategory.Q).obj model) ∧
    DerivedCategory.finiteTorAmplitude _ ((_root_.DerivedCategory.Q).obj model)
  i : Index k L
  term : ℤ → towerModule (A := A) (stage y i.val)
  termIso : ∀ n, Nonempty ((pull A (projection y i.val)).obj
    ((DerivedCategory.singleFunctor _ 0).obj (term n)) ≅
      (DerivedCategory.singleFunctor _ 0).obj (model.X n))

/-- Termwise finite-stage models for a bounded constructible finite-Tor complex.

Source: Stacks Project, Etale Cohomology, Tags 03TT and 09YU (3), after choosing a
bounded constructible finite-Tor representative (taken flat in the construction).  The proof
presents each nonzero term by finite affine-etale free sums, descends the finitely many affine
objects and matrix sections along
the affine inverse-limit tower, and uses directedness to refine every stage to one common
intermediate field.  Pullback comparison gives the displayed term isomorphisms; no
differential compatibility is asserted in this statement.
(blueprint: lem-sf-finite-etale-tower-constructible-term-descent) -/
theorem finiteEtaleTower_constructible_term_stage_descent
    [Finite k] [Algebra.IsSeparable k L]
    [LocallyOfFiniteType y] [QuasiCompact y] [IsSeparated y]
    (K : towerComplex A (limitScheme (L := L) y))
    (hK : constantModelBoundedConstructible
        (Profinite.continuousCoefficientRingObj A) (limitScheme (L := L) y)
        ((_root_.DerivedCategory.Q).obj K) ∧
      DerivedCategory.finiteTorAmplitude _ ((_root_.DerivedCategory.Q).obj K)) :
    Nonempty (TermStageData y A K) := by
  sorry

end AlgebraicGeometry.ProEtale.FiniteEtaleTower
