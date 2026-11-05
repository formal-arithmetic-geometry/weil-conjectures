/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Adjunction.Unique
public import WeilConjectures.CategoryTheory.SiteAlgebraicCompositionUnit

/-!
# Algebraic transport of unit-normalized site composition and identity

Source: Stacks Project, Sites, Tags 03CB, 00VE, 00WX, 00WH and 00YV;
Modules on Sites, Tag 03D2 (blueprint: lem-pur-site-algebraic-composition-unit).

The composite inverse image is the specified comma-colimit/sheafification construction.
Its comparison is obtained from the specified adjunctions, without choosing another unit.
The predicates below spell out the algebraic clauses using the recorded presentations;
they do not choose new ring or module structures.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

universe uC vC uD vD uE vE w s

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

namespace CategoryTheory

noncomputable section Transport

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

end Transport

noncomputable section AlgebraicTransport

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]

end AlgebraicTransport

noncomputable section Lift

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} [PreservesFiniteLimits F]
  (γ : F ⟶ G) {R : Sheaf J CommRingCat.{s}} {R₀ R₁ : Sheaf K CommRingCat.{s}}
  (A₀ : SheafOfModules.AlgebraicInverseImageOfUniverses F R R₀)
  (A₁ : SheafOfModules.AlgebraicInverseImageOfUniverses G R R₁)

end Lift

noncomputable section FinishTransport

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
  [K.HasSheafCompose (CategoryTheory.forget CommRingCat.{s} ⋙ uliftFunctor.{s, s})]
  [K.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{s} ⋙ uliftFunctor.{s, s})]
  {F G : Sheaf J (Type s) ⥤ Sheaf K (Type s)} [PreservesFiniteLimits F]
  (γ : F ≅ G) {R : Sheaf J CommRingCat.{s}} {R₀ R₁ : Sheaf K CommRingCat.{s}}
  (A₀ : SheafOfModules.AlgebraicInverseImageOfUniverses F R R₀)
  (A₁ : SheafOfModules.AlgebraicInverseImageOfUniverses G R R₁)

end FinishTransport

end CategoryTheory
