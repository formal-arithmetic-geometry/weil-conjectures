/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

/-!
# Powerset codes for actual module subsheaves

Source: blueprint main-20261015, integral-heart triangulated proof, paragraph (2),
final sentence, expanded in the small-site image-subsheaf representatives lemma
(blueprint: def-sfb-small-site-module-subsheaf-codes).

These definitions retain the actual subsets, not their isomorphism classes.
The existing presheaf-submodule construction supplies all inherited operations.
-/

@[expose] public section

universe u

open CategoryTheory

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- The product of the powersets of the section sets.
Source: integral-heart triangulated proof, paragraph (2), final sentence, expanded
in the small-site image-subsheaf lemma
(blueprint: def-sfb-small-site-module-subsheaf-codes). -/
def SectionSubsetFamily (P : ringedSiteModules.{u} R) : Type u :=
  ∀ X : Cᵒᵖ, Set (P.val.obj X)

/-- The subset families that are restriction-stable submodules and are sheaves.
Source: integral-heart triangulated proof, paragraph (2), final sentence, expanded
in the small-site image-subsheaf lemma
(blueprint: def-sfb-small-site-module-subsheaf-codes).
`PresheafOfModules.Submodule` already encodes the inherited operations and restrictions. -/
def IsModuleSubsheafCode (P : ringedSiteModules.{u} R)
    (s : SectionSubsetFamily P) : Prop :=
  ∃ N : P.val.Submodule,
    (∀ X : Cᵒᵖ, (N.obj X : Set (P.val.obj X)) = s X) ∧
      Presheaf.IsSheaf J N.toPresheafOfModules.presheaf

/-- The subset `E` of the product of powersets `D`.
Source: integral-heart triangulated proof, paragraph (2), final sentence, expanded
in the small-site image-subsheaf lemma
(blueprint: def-sfb-small-site-module-subsheaf-codes). -/
def ModuleSubsheafCode (P : ringedSiteModules.{u} R) : Type u :=
  {s : SectionSubsetFamily P // IsModuleSubsheafCode P s}

/-- Recover the uniquely determined restriction-stable submodule from its subset code.
Source: integral-heart triangulated proof, paragraph (2), final sentence, expanded
in the small-site image-subsheaf lemma
(blueprint: def-sfb-small-site-module-subsheaf-codes).
The witness is determined by its carriers; choice uses the actual membership proof,
with no postponed existence theorem. -/
noncomputable def ModuleSubsheafCode.submodule {P : ringedSiteModules.{u} R}
    (s : ModuleSubsheafCode P) : P.val.Submodule :=
  s.property.choose

/-- The actual module sheaf with inherited section modules and restrictions.
Source: integral-heart triangulated proof, paragraph (2), final sentence, expanded
in the small-site image-subsheaf lemma
(blueprint: def-sfb-small-site-module-subsheaf-codes). -/
noncomputable def ModuleSubsheafCode.toSheaf {P : ringedSiteModules.{u} R}
    (s : ModuleSubsheafCode P) : ringedSiteModules.{u} R :=
  ⟨s.submodule.toPresheafOfModules, s.property.choose_spec.2⟩

/-- The actual subset inclusion into the specified target.
Source: integral-heart triangulated proof, paragraph (2), final sentence, expanded
in the small-site image-subsheaf lemma
(blueprint: def-sfb-small-site-module-subsheaf-codes). -/
noncomputable def ModuleSubsheafCode.ι {P : ringedSiteModules.{u} R}
    (s : ModuleSubsheafCode P) : s.toSheaf ⟶ P :=
  ⟨s.submodule.ι⟩

end SheafOfModules
