/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.KrullDimension
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs

import WeilConjectures.AlgebraicGeometry.Bertini.BertiniUniversalBaseChange
import WeilConjectures.AlgebraicGeometry.Bertini.BertiniUniversalFamily
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.Topology.KrullDimension
import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.GenericGeometricIrreducibilityShrink
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Geometric irreducibility of a general member of a linear system

Source: Stacks Project, More on Morphisms, Tag 0G4F, lemma-bertini-irreducible,
in Varieties Situation 0G47 (blueprint: lem-zl-bertini-irreducible-member).

The helper constructs the member over an extension field using the canonical tensor-pullback
unit, then uses the recorded zero-scheme construction. Codimension is `Order.coheight` on
irreducible closed subsets, ordered by inclusion. Components of a closed subset are its maximal
irreducible closed subsets. Generality is written out using all extension-field points of a
nonempty open in affine coordinate space.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj

attribute [local irreducible] linearSystemMemberIdeal bertiniUniversalIdeal

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem tensorUnit_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) :
    Scheme.Modules.tensorSectionsUnit f M =
      (show Γ(M, ⊤) ⟶ Γ((Scheme.Modules.tensorPullback f).obj M, ⊤) from
        Scheme.Modules.Hom.app
          ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)).unit.app M)
          ⊤) := by
  unfold Scheme.Modules.tensorSectionsUnit
  have hi : (homOfLE f.preimage_top.ge).op = 𝟙 (op (⊤ : X.Opens)) := rfl
  erw [hi, ((Scheme.Modules.tensorPullback f).obj M).presheaf.map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
end AlgebraicGeometry
