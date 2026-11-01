/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ProperBaseChange.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import WeilConjectures.AlgebraicGeometry.Bertini.BertiniFiniteCoverBaseCodimension
import WeilConjectures.AlgebraicGeometry.Bertini.BertiniFiniteCoverTransverseComponent
import WeilConjectures.AlgebraicGeometry.Bertini.BertiniIrreducibleMember
import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Simultaneous irreducibility on a finite étale cover

Source: main-20261015 blueprint, proof of `lem-zl-bertini-finite-cover-curve`, paragraph 3;
Stacks Project, Tag 0G4F (blueprint: lem-zl-bertini-finite-cover-irreducible-system).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules Opposite MonoidalCategory

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
end

end AlgebraicGeometry
