/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.StdBasis
import WeilConjectures.AlgebraicGeometry.Bertini.BertiniPrescribedPointSmoothSystem
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.DeligneLaumon.GeneratingSectionsImmersionReindex
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateModel
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus

/-! # An affine coordinate presentation of the prescribed-point smooth system

Source: the current blueprint, finite-cover-curve proof, paragraph 2;
Stacks Project, Tags 0FD5 and 0FD6.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules

noncomputable section

attribute [local instance] cachedSheafify cachedWEquals
attribute [local instance 2000]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensCarrierAbPresheaf
attribute [local irreducible] tensorPullback tensorPullbackObj
  ProjectiveSpace.homOfGeneratingSections tensorSectionsUnit prescribedPointCombination
  prescribedPointRestrictedFamily prescribedPointMember prescribedPointVanishes
attribute [local irreducible] ProjectiveSpace Proj Proj.toSpecBase

private theorem tensorUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    tensorSectionsUnit f M =
      (show Γ(M, ⊤) ⟶ Γ((tensorPullback f).obj M, ⊤) from
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).app ⊤) := by
  unfold tensorSectionsUnit
  have hi : (homOfLE f.preimage_top.ge).op = 𝟙 (op (⊤ : X.Opens)) := rfl
  erw [hi, ((tensorPullback f).obj M).presheaf.map_id, Category.comp_id]

set_option maxHeartbeats 1000000 in
-- The dependent finite-system interface and its section conversions use this budget.
end

end AlgebraicGeometry
