/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.AlternatingCechTotalComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # The explicit alternating Čech model over an affine base

Source: Stacks Project, Tag 0A1D, finite affine Čech calculation.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Restrict the increasing-tuple section complex to A, sheafify on Spec A, and
extend by zero to integer degrees. No choice of a representative is made.
Source: blueprint `lem-pc-rf-base-change-flat-module`, Steps 2--3; Stacks Tag 0A1D.
(blueprint: def-pc-affine-alternating-cech-model). -/
noncomputable def affineAlternatingCechModel
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A)
    {r : ℕ} (U : Fin r → X.Opens) (G : X.Modules) :
    CochainComplex (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) ℤ :=
  ((ModuleCat.restrictScalars (((Scheme.ΓSpecIso A).inv ≫ f.appTop).hom) ⋙
      tilde.functor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((alternatingCechComplex U G.presheafModuleCat).extend ComplexShape.embeddingUpNat)

end AlgebraicGeometry
