/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.FlatRingedDiagramInput.FlatRingedDiagramRestrictionDefs
public import WeilConjectures.CategoryTheory.ExactAdjointTowerModels.ExactAdjointTowerModels
import WeilConjectures.Algebra.Homology.ProperBaseChange.FlatRestrictionExactLeftAdjoint
import WeilConjectures.CategoryTheory.ProperBaseChange.SmallModuleDiagramsGrothendieck
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp

/-! # Flat scalars and the normalized direct-image/strict-limit square

Source: blueprint main-20261015, proper base change, completed exchange coherence,
second paragraph; scalar supplement using Stacks Tags 0A07, 08BJ, 070I, 070Y and 070K
(blueprint: lem-weil-pbc-flat-scalar-tower-limit-square).

The auxiliary structures merely bundle the universal units and their normalization
identities. Ordinary scalar-limit maps are fixed by `limit.post`, which sends a
compatible family to the same family. Positive tower level n+1 is indexed by n : ℕ.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u w uA uB uA' uB' vA vB vA' vB'

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ExactAdjointTowerModels

namespace CategoryTheory.FlatScalarTowerLimit

-- Infer the category from the equation before elaborating its common final factor.

-- Comparisons can be descended directly from the two units on K-injectives.

section Normalizations

variable {A : Type uA} {B : Type uB} {A' : Type uA'} {B' : Type uB'}
  [Category.{vA} A] [Category.{vB} B] [Category.{vA'} A'] [Category.{vB'} B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} A'] [HasDerivedCategory.{w} B']

attribute [instance] limitAdditive

variable [HasLimitsOfShape ℕᵒᵖ A] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ A)] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]

end Normalizations

-- The normalization fields have an abstract categorical API. Keeping the diagram
-- chase at this level avoids repeatedly unfolding the sheaf and chosen-limit data.
-- The normalization chase retains arbitrary localization universes and all unit factors.
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {K : GrothendieckTopology C} {H : GrothendieckTopology D}

-- Elaborate the comparison interfaces and the two scalar-restriction adjunctions.
end CategoryTheory.FlatScalarTowerLimit
