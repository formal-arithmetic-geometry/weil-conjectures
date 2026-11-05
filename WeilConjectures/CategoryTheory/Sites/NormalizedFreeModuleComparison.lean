/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
public import WeilConjectures.CategoryTheory.SiteCoveringAxioms
public import Mathlib.LinearAlgebra.FreeModule.Basic

import WeilConjectures.CategoryTheory.Sites.FreeModuleUniversalProperty
import Mathlib.CategoryTheory.Sites.CartesianMonoidal

/-!
# Conditional calculus of normalized free-module comparisons

Source: Stacks Project, Modules on Sites, Tag 08TQ (lemma-pullback-differentials),
free-module identifications, and Tag 04BL (lemma-universal-module), generator extensions
(auxiliary; not a blueprint node).

The free sheaves, generators, and simultaneous coefficient/generator changes are the
existing `SheafFreeModule.free`, `generator`, and `change`. No adjunction is assumed for
the set-sheaf functors. Equalities of semilinear maps are expressed on their underlying
sheaves; this forgetful description is faithful. The explicit `ULift` identifications
are those of the recorded algebraic inverse-image interface.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe w wI uC vC uD vD uH vH

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.SheafFreeModule

variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
  {D : Type uD} [Category.{vD} D] [EssentiallySmall.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

-- Cache the existing sheaf-composition witnesses once for each site.
local instance : J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
local instance : J.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : J.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
local instance : K.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : K.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

attribute [-instance] hasSheafCompose_of_preservesMulticospan in
/-- The stated representing hypothesis is precisely bijectivity of restriction along
L of the canonical generator, for every target module sheaf. Source: Stacks 04BL and
08TQ, conditional free identification
(auxiliary; not a blueprint node). -/
def HasTransportedFreeUniversalProperty
    (L : Sheaf J (Type w) ⥤ Sheaf K (Type w))
    {B : Sheaf J CommRingCat.{w}} {BI : Sheaf K CommRingCat.{w}}
    (F : SheafOfModules.AlgebraicInverseImageOfUniverses.{uC, vC, uD, vD, w, w} L B BI)
    (E : Sheaf J (Type w)) : Prop :=
  ∀ M : SheafOfModules.{w} (ring BI),
    Function.Bijective (fun h : F.modules.obj ((free B).obj E) ⟶ M ↦
      L.map (generator B E) ≫ F.moduleUnderlying.inv.app ((free B).obj E) ≫
        (moduleSets BI).map h)

variable {H : Type uH} [Category.{vH} H] [EssentiallySmall.{w} H]
  {T : GrothendieckTopology H}

local instance : T.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
local instance : T.HasSheafCompose (forget CommRingCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance
local instance : T.HasSheafCompose (forget AddCommGrpCat.{w} ⋙ uliftFunctor.{w, w}) := inferInstance

end CategoryTheory.SheafFreeModule
