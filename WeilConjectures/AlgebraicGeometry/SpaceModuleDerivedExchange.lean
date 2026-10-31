/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceAffineHomComparison
public import WeilConjectures.AlgebraicGeometry.SpaceDerivedPullback

/-! # Canonical derived exchange for algebraic-space modules

Source: Stacks Project, sites-cohomology.tex, Tags 07A6 and 07A7;
spaces-perfect.tex, Tag 08IR, first proof sentence
(blueprint: def-sfb-space-module-derived-exchange).

The map is the adjoint of the pulled counit, using the recorded normalized composition
and adjunction. It is defined for every commuting square, without an invertibility claim.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S}
  [HasDerivedCategory.{w} X.SmallModules] [HasDerivedCategory.{w} Y.SmallModules]
  [HasDerivedCategory.{w} X'.SmallModules] [HasDerivedCategory.{w} Y'.SmallModules]

/-- Derived exchange, defined as the adjoint of the pulled counit.
Source: Stacks, Tags 07A6 and 07A7; spaces-perfect.tex, Tag 0A1K
(blueprint: def-sfb-space-module-derived-exchange). -/
def moduleDerivedExchange (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (h : X' ⟶ X)
    (w : h ≫ f = f' ≫ g) (A : X.DerivedModules) :
    (derivedTensorPullback g).obj ((derivedDirectImage f).obj A) ⟶
      (derivedDirectImage f').obj ((derivedTensorPullback h).obj A) :=
  (spaceDerivedAdjunction f').homEquiv _ _
    ((spaceDerivedPullbackComp g f').inv.app ((derivedDirectImage f).obj A) ≫
      (eqToIso (congrArg (fun k : X' ⟶ Y ↦
        (derivedTensorPullback k : Y.DerivedModules ⥤ X'.DerivedModules)) w.symm)).hom.app
        ((derivedDirectImage f).obj A) ≫
      (spaceDerivedPullbackComp f h).hom.app ((derivedDirectImage f).obj A) ≫
      (derivedTensorPullback h).map ((spaceDerivedAdjunction f).counit.app A))

end AlgebraicGeometry.AlgebraicSpace
