/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.HomTensor.Basic

/-! # Identifying the sheaf dual-tensor comparison with the categorical comparison

Source: Stacks Project, Modules, Example 0FNV, the canonical tensor-to-endomorphism map.
(blueprint: lem-ag-dual-tensor-hom-comparison)
-/

@[expose] public section

universe u

open CategoryTheory

section
universe v

open MonoidalCategory

section
variable {C : Type u} [Category C] [MonoidalCategory C]
  {D : Type v} [Category D] [MonoidalCategory D]

end

namespace SheafOfModules
set_option hygiene false in
local notation "𝓡" => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "𝓢" => PresheafOfModules.sheafification.{u} (𝟙 (𝓡).obj)
set_option hygiene false in
local notation "adj" => PresheafOfModules.sheafificationAdjunction.{u} (𝟙 (𝓡).obj)
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {R : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
attribute [local instance] monoidalCategory symmetricCategory monoidalClosed
end SheafOfModules

end

namespace AlgebraicGeometry.Scheme.Modules

end AlgebraicGeometry.Scheme.Modules
