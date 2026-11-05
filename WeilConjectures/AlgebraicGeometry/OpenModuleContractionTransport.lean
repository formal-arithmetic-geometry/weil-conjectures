/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! # Transport of a module contraction on an open subscheme

Source: Stacks Project, Tags 08DL, 08DQ and 03EO; the sectionwise
open-site reindexing construction of `Scheme.Modules.overEquiv`.
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace SheafOfModules
attribute [local instance] monoidalCategory symmetricCategory
variable {C : Type u} [Category.{u} C] [Quiver.IsThin C]
  {J : GrothendieckTopology C} [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify J AddCommGrpCat.{u}]
  (R : Sheaf J CommRingCat.{u})
set_option quotPrecheck false in
set_option hygiene false in
local notation "Q" => (sheafCompose J (forget₂ CommRingCat RingCat)).obj R
set_option quotPrecheck false in
set_option hygiene false in
local notation "Mod" => SheafOfModules.{u} Q

-- Free representables provide local sections and embed in the unit on a thin site.

-- Maps out of a sheaf tensor product are determined by the presheaf tensor.

-- Subobjects of the unit determine the whole natural family.

variable {D : Type u} [Category.{u} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasSheafify K AddCommGrpCat.{u}]
  (S : Sheaf K CommRingCat.{u})
set_option quotPrecheck false in
set_option hygiene false in
local notation "ModD" => SheafOfModules.{u}
  ((sheafCompose K (forget₂ CommRingCat RingCat)).obj S)

-- Compare the two natural families after pulling back through the fully faithful functor.

end SheafOfModules

namespace AlgebraicGeometry
attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local instance] openModuleOver_isThin

attribute [local irreducible] Scheme.Modules.overEquiv
attribute [local irreducible] SheafOfModules.tensorHomEquiv

-- Preserve the established names of the nondependent forall hypotheses.

end AlgebraicGeometry
