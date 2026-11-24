/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

public import Mathlib.LinearAlgebra.ExteriorPower.Basis

import WeilConjectures.AlgebraicGeometry.KoszulSelfExtQuotientFrame
import WeilConjectures.AlgebraicGeometry.ClosedImmersionQuotientFramePullback

/-! # A finite free chart for self Ext after tensor pullback

## References

* Stacks Project, Tag 0BQY, Lemma 48.15.4.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- On a Koszul-regular affine chart, the pulled-back self Ext sheaf is free on
increasing subsets of the given generators (Stacks, Tag 0BQY). This is a sheaf assertion
on the chart; no stalk, auxiliary open restriction, or conormal dual is involved. -/
theorem koszulRegularImmersion_self_ext_pullback_local_frame
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (U : Y.affineOpens) (n : ℕ)
    (m : ℕ) (f : Fin m → Γ(Y, U.1))
    (hf : Ideal.span (Set.range f) = i.ker.ideal U)
    (hreg : RingTheory.Sequence.IsKoszulRegular f) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let H := derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf
    let G := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (n : ℤ)).obj
        (H.obj (op (S.obj B), S.obj B))
    Nonempty ((((Scheme.Modules.tensorPullback i).obj G).over (i ⁻¹ᵁ U.1)) ≅
      SheafOfModules.free (ULift.{u} (Set.powersetCard (Fin m) n))) := by
  classical
  dsimp only
  obtain ⟨e⟩ := koszul_self_ext_quotient_frame i U n m f hf hreg
  exact closedImmersion_quotient_frame_pullback i U.1 _ _ e

end AlgebraicGeometry
