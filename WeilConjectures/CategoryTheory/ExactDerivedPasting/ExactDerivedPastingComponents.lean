/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import all WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows

/-! # Components for finite exact-derived pasting

Source: Stacks, Tags 015F and 04VG.
(blueprint: lem-cbc-exact-derived-pasting-components)

The public congruence theorem and the private component calculations let applications
use finite expression trees without unfolding sheaf inverse-image constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option linter.unusedSimpArgs false
universe u t v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProEtale.StrictTower
namespace CategoryTheory.ExactDerivedPasting

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Generic
variable {I : Type t} (C : I → Type u) [∀ i, Category.{v} (C i)]
  [∀ i, Abelian (C i)] [∀ i, HasDerivedCategory.{w} (C i)]

attribute [local instance] exactEdgeAdditive

end Generic

section TermwiseComponents
variable {A D E F : Type t} [Category.{v} A] [Category.{v} D]
  [Category.{v} E] [Category.{v} F]

end TermwiseComponents

section TowerLaws
variable {I : Type t} (C : I → Type u) [∀ i, Category.{v} (C i)]

end TowerLaws

end CategoryTheory.ExactDerivedPasting

namespace AlgebraicGeometry.ProEtale.StrictTower
variable (B : Type (u + 1)) [CommRing B]

section PastingProofs

open CategoryTheory.ExactDerivedPasting
set_option linter.unusedSimpArgs false
attribute [local irreducible] Functor.leftAdjoint modulePullback
attribute [local irreducible] singleAlpha alpha beta gComp jComp squareG
attribute [local irreducible] moduleGComp moduleSquareG openBetaModule openBetaModuleJComp

attribute [local instance] clopenTowerAbelian towers_hasDerivedCategory
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

end PastingProofs

end AlgebraicGeometry.ProEtale.StrictTower
