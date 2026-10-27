/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-! # Exterior sheaves on a ringed site

Source: Stacks Project, Modules on Sites, Tag 03CY, and Algebra, Tag 00DM.
(blueprint: def-sfb-site-exterior-sheaf)

The sectionwise exterior presheaf is the existing upstream construction. Only its
sheafification, its unit on wedges, and its induced maps are assembled here.
-/

@[expose] public section

universe u v w

open CategoryTheory

namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {B : Sheaf J CommRingCat.{w}}

/-- Sheafify the existing sectionwise exterior-power presheaf.
Source: Stacks 03CY and 00DM (blueprint: def-sfb-site-exterior-sheaf). -/
noncomputable def siteExteriorPower
    (Q : ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B))
    (n : ℕ) : ringedSiteModules.{w}
      ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B) :=
  (PresheafOfModules.sheafification (𝟙 _)).obj
    (PresheafOfModules.exteriorPower (R := B.obj) Q.val n)

/-- The sectionwise wedge followed by the module sheafification unit, including the empty wedge.
Source: Stacks 03CY and 00DM (blueprint: def-sfb-site-exterior-sheaf). -/
noncomputable def siteExteriorWedge
    (Q : ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B))
    (n : ℕ) (U : Cᵒᵖ) (x : Fin n → Q.val.obj U) :
    (siteExteriorPower Q n).val.obj U :=
  ((PresheafOfModules.sheafificationAdjunction
      (R := (sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B) (𝟙 _)).unit.app
    (PresheafOfModules.exteriorPower (R := B.obj) Q.val n)).app U
      (exteriorPower.ιMulti (B.obj.obj U) n x)

/-- Sectionwise exterior maps commute with semilinear restrictions.
Source: Stacks 00DM, functoriality of the alternating quotient
(blueprint: def-sfb-site-exterior-sheaf).
Proof: on a pure wedge both composites give the wedge of the restricted images.
Naturality of the module morphism equates these tuples. Pure wedges generate the
exterior power, so its linear universal property equates the composites. -/
theorem siteExteriorPresheafHom_naturality
    {Q Q' : ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)}
    (g : Q ⟶ Q') (n : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V) :
    (PresheafOfModules.exteriorPower (R := B.obj) Q.val n).map f ≫
        (ModuleCat.restrictScalars
          (((B.obj ⋙ forget₂ CommRingCat.{w} RingCat.{w}).map f).hom)).map
          (ModuleCat.ofHom
            (X := (PresheafOfModules.exteriorPower (R := B.obj) Q.val n).obj V)
            (Y := (PresheafOfModules.exteriorPower (R := B.obj) Q'.val n).obj V)
            (exteriorPower.map (R := B.obj.obj V) n (g.val.app V).hom)) =
      ModuleCat.ofHom
        (X := (PresheafOfModules.exteriorPower (R := B.obj) Q.val n).obj U)
        (Y := (PresheafOfModules.exteriorPower (R := B.obj) Q'.val n).obj U)
        (exteriorPower.map (R := B.obj.obj U) n (g.val.app U).hom) ≫
        (PresheafOfModules.exteriorPower (R := B.obj) Q'.val n).map f := by
  sorry

/-- The actual sectionwise exterior linear maps, with their naturality proof named separately.
Source: Stacks 00DM (blueprint: def-sfb-site-exterior-sheaf). -/
noncomputable def siteExteriorPresheafHom
    {Q Q' : ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)}
    (g : Q ⟶ Q') (n : ℕ) :
    PresheafOfModules.exteriorPower (R := B.obj) Q.val n ⟶
      PresheafOfModules.exteriorPower (R := B.obj) Q'.val n where
  app U := ModuleCat.ofHom
        (X := (PresheafOfModules.exteriorPower (R := B.obj) Q.val n).obj U)
        (Y := (PresheafOfModules.exteriorPower (R := B.obj) Q'.val n).obj U)
        (exteriorPower.map (R := B.obj.obj U) n (g.val.app U).hom)
  naturality f := siteExteriorPresheafHom_naturality g n f

/-- Sheafification of the sectionwise exterior maps.
Source: Stacks 03CY and 00DM (blueprint: def-sfb-site-exterior-sheaf). -/
noncomputable def siteExteriorHom
    {Q Q' : ringedSiteModules.{w} ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).obj B)}
    (g : Q ⟶ Q') (n : ℕ) : siteExteriorPower Q n ⟶ siteExteriorPower Q' n :=
  (PresheafOfModules.sheafification (𝟙 _)).map (siteExteriorPresheafHom g n)

end SheafOfModules
