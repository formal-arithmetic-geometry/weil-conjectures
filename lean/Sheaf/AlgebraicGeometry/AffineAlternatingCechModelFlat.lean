/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q3
-/
module

public import Sheaf.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Bounded flat terms in the affine alternating Čech model

Source: blueprint `lem-pc-rf-base-change-flat-module`, Steps 2--3; Stacks Tag 0A1D.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- The explicit finite alternating model is termwise flat over
its affine base. This is about the ordinary complex, without any derived map.
Source: blueprint `lem-pc-rf-base-change-flat-module`, Steps 2--3; Stacks Tag 0A1D.
(blueprint: lem-pc-affine-alternating-cech-model-flat).

Proof: Separatedness over an affine scheme makes all finite intersections of affine
opens affine. Apply IsFlatOver to each such intersection and the top affine open
of Spec A. Transport the resulting flatness through GammaSpecIso to the A-action
in restrictScalars. Each term is a finite product of these flat A-modules and is
therefore flat. Sheafification preserves this property: its stalk at a prime is
localization of the section module, flat over the localized ring. Negative-degree
terms are zero by extension and are flat; the empty product terms in degrees
p >= r are likewise zero. The argument includes r = 0 and zero rings. -/
theorem affineAlternatingCechModel_flat
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    {r : ℕ} (U : Fin r → X.Opens) (haffine : ∀ i, IsAffineOpen (U i))
    (G : X.Modules) (hflat : Scheme.Modules.IsFlatOver G f) :
    ∀ i : ℤ, SheafOfModules.IsFlat ((affineAlternatingCechModel f U G).X i) := by
  sorry

end AlgebraicGeometry
