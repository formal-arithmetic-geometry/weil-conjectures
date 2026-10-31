/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveSpaceFunctorOfPoints
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
import WeilConjectures.AlgebraicGeometry.Bertini.BertiniUniversalFamily
import Mathlib.Topology.KrullDimension
import Mathlib.LinearAlgebra.Basis.Defs
import WeilConjectures.AlgebraicGeometry.ProjectiveSpaceReindexIsIso
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan
import WeilConjectures.AlgebraicGeometry.InvertibleStalkLinearEquiv
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus

/-!
# Smooth general members of an immersive linear system

Source: Stacks Project, Varieties, Situation 0FD3 and Lemma 0FD6
(blueprint: lem-zl-bertini-smooth-member).
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry

noncomputable section

/-- A family of top-open sections as compatible global sections, through the existing
unit/global-section equivalence. Source: Stacks Project, Situation 0FD3
(blueprint: lem-zl-bertini-smooth-member). -/
def bertiniSectionFamily {Y : Scheme.{u}} (L : Y.Modules) {I : Type u}
    (s : I → Γ(L, ⊤)) : I → L.sections :=
  fun i ↦ (SheafOfModules.unitHomEquiv L) (Scheme.Modules.homOfGlobalSection L (s i))

open Scheme.Modules

private def tensorComparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    tensorPullback f ≅ Scheme.Modules.pullback f :=
  (Classical.choose (exists_tensorPullbackAdjunction f)).leftAdjointUniq
    (pullbackPushforwardAdjunction f)

attribute [local irreducible] tensorPullback tensorPullbackObj

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    tensorSectionsUnit f M =
      (show Γ(M, ⊤) ⟶ Γ((tensorPullback f).obj M, ⊤) from
        ((Classical.choose (exists_tensorPullbackAdjunction f)).unit.app M).app ⊤) := by
  unfold tensorSectionsUnit
  have hi : (homOfLE f.preimage_top.ge).op = 𝟙 (op (⊤ : X.Opens)) := rfl
  erw [hi, ((tensorPullback f).obj M).presheaf.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorPullback_invertible {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) [M.IsInvertible] : ((tensorPullback f).obj M).IsInvertible :=
  IsInvertible.of_iso ((tensorComparison f).app M).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [local instance] coordinateReindex_isIso

attribute [local irreducible] ProjectiveSpace.homOfIsFreeGenerator

end

end AlgebraicGeometry
