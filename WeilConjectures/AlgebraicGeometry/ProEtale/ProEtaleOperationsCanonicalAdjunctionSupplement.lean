/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-!
# Canonically normalized pro-etale module adjunctions

Source: Stacks Project, Modules on Sites, lemma-adjoint-push-pull-modules;
Cohomology on Sites, Tag 07A6 (blueprint: def-weil-pbc-proetale-operations).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules

-- First transpose the sectionwise tensor maps, then use the sheafification adjunction.
-- These helpers work for sites in arbitrary object and morphism universes.

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  {A B : Sheaf J CommRingCat.{u}} (a : A ⟶ B)
set_option hygiene false in
local notation "𝓡" S => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj S

end SheafOfModules

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

end AlgebraicGeometry.Scheme
