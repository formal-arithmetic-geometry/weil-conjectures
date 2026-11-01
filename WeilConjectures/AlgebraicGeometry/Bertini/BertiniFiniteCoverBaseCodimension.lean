/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Basis.Defs
public import WeilConjectures.AlgebraicGeometry.Compactification.PureDimension
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSections
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction

import WeilConjectures.AlgebraicGeometry.GeneratingSectionsStalkSpan
import WeilConjectures.AlgebraicGeometry.InvertibleStalkLinearEquiv
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import WeilConjectures.RingTheory.FiniteTypeDomainDimensionLocalRingLocalization
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.LocalRing.Module

/-! # BertiniFiniteCoverBaseCodimension

Source: blueprint paragraph 3 of the finite-cover Bertini argument
(blueprint: lem-zl-bertini-finite-cover-base-codimension).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

open Scheme.Modules Opposite MonoidalCategory

noncomputable section

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
end

end AlgebraicGeometry
