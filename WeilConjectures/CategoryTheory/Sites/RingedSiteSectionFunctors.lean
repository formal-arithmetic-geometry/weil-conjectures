/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.UnboundedSectionsLocalization
public import WeilConjectures.CategoryTheory.SubterminalDerivedImageCalculus
public import WeilConjectures.AlgebraicGeometry.LocalizeRingedSiteMorphismGeneral

/-! # Section functors and structural module maps on small ringed sites

Source: Stacks Project, Cohomology on Sites, Tag 0D6H (lemma-Leray-unbounded),
and Modules on Sites, Tag 04J0 (lemma-localize-morphism-ringed-sites)
(blueprint: def-sfb-ringed-site-section-functors).

These aliases give definition-node ownership to the existing section evaluation,
Grothendieck structure, structural module map and additive pushforward structure.
They reuse the unchanged constructions and instances; no theorem conclusion is used.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory Opposite

namespace CategoryTheory.RingedSiteSectionFunctors

/-- Evaluation at a site object, followed by forgetting scalars.
Source: Stacks Project, Tag 0D6H (lemma-Leray-unbounded)
(blueprint: def-sfb-ringed-site-section-functors). -/
abbrev sectionEvaluation {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) (V : C) : ringedSiteModules.{u} R ⥤ AddCommGrpCat.{u} :=
  UnboundedSectionsLocalization.evaluation R V

/-- The existing small-site Grothendieck abelian structure, without a new instance.
Source: Stacks Project, Tag 0D6H, small-site K-injective setup
(blueprint: def-sfb-ringed-site-section-functors). -/
abbrev modulesGrothendieck {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u}) : IsGrothendieckAbelian.{u} (ringedSiteModules.{u} R) :=
  UnboundedSectionsLocalization.modulesGrothendieck R

/-- The existing componentwise additive structure on continuous module pushforward.
Source: Stacks Project, Tag 04J0 (lemma-localize-morphism-ringed-sites)
(blueprint: def-sfb-ringed-site-section-functors). -/
abbrev pushforwardAdditive {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {F : D ⥤ C} [F.IsContinuous K J]
    {S : Sheaf K RingCat.{u}} {R : Sheaf J RingCat.{u}}
    (a : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K J).obj R) :
    (SheafOfModules.pushforward.{u} a).Additive :=
  SubterminalImageCalculus.pushforwardAdditive a

/-- The structural morphism of underlying ring sheaves used by module direct image.
Source: Stacks Project, Tag 04J0 (lemma-localize-morphism-ringed-sites)
(blueprint: def-sfb-ringed-site-section-functors). -/
abbrev sectionModuleMap {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J]
    {S : Sheaf K CommRingCat.{u}} {R : Sheaf J CommRingCat.{u}}
    (a : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} K J).obj R) :
    (sheafCompose K (forget₂ CommRingCat RingCat)).obj S ⟶
      (F.sheafPushforwardContinuous RingCat.{u} K J).obj
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) :=
  SheafOfModules.ringedSiteModuleMap F a

end CategoryTheory.RingedSiteSectionFunctors
