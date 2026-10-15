/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NJ
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Ideals on a ringed site

Source: Stacks Project, Modules on Sites, finite type ideals; Algebraization, Tags 0999
and 099I (blueprint: def-weil-pbc-ringed-site-ideal).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace CategoryTheory

/-- Forget only commutativity when forming the module category of a ringed site.
Source: Stacks Project, Modules on Sites (blueprint: def-weil-pbc-ringed-site-ideal).
-/
abbrev siteModuleRings {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : Sheaf J RingCat.{u} :=
  (sheafCompose J (forget₂ CommRingCat RingCat)).obj R


/-- An ideal subsheaf: ideals of sections, stable under restriction, with local membership.
Source: Stacks Project, Modules on Sites, sheaves of ideals; Algebraization, Tag 0999
(blueprint: def-weil-pbc-ringed-site-ideal). -/
structure RingedSiteIdeal {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) where
  /-- The ideal of sections on each object. -/
  sections (U : C) : Ideal (R.obj.obj (op U))
  /-- Restrictions preserve the ideal. -/
  restriction {U V : C} (g : V ⟶ U) (a : R.obj.obj (op U)) :
    a ∈ sections U → R.obj.map g.op a ∈ sections V
  /-- Ideal membership can be checked on a covering sieve. -/
  local_mem (U : C) (a : R.obj.obj (op U)) (S : Sieve U) :
    S ∈ J U → (∀ (V : C) (g : V ⟶ U), S g → R.obj.map g.op a ∈ sections V) →
      a ∈ sections U

namespace RingedSiteIdeal

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{u}}

/-- Restriction on the ideals of sections, as a semilinear module map.
Source: Stacks Project, Modules on Sites, ideal subsheaves
(blueprint: def-weil-pbc-ringed-site-ideal). -/
noncomputable def restrictionMap (I : RingedSiteIdeal R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    ModuleCat.of (R.obj.obj X) (I.sections X.unop) ⟶
      (ModuleCat.restrictScalars ((siteModuleRings R).obj.map f).hom).obj
        (ModuleCat.of (R.obj.obj Y) (I.sections Y.unop)) :=
  ModuleCat.ofHom
    (X := ModuleCat.of (R.obj.obj X) (I.sections X.unop))
    (Y := (ModuleCat.restrictScalars ((siteModuleRings R).obj.map f).hom).obj
      (ModuleCat.of (R.obj.obj Y) (I.sections Y.unop)))
    { toFun := fun a => ⟨R.obj.map f a, I.restriction f.unop a a.property⟩
      map_add' := fun a b => Subtype.ext (map_add (R.obj.map f).hom a.val b.val)
      map_smul' := fun r a => Subtype.ext (map_mul (R.obj.map f).hom r a.val) }

/-- Identity law for restriction on an ideal.
Source: Stacks Project, Modules on Sites (blueprint: def-weil-pbc-ringed-site-ideal).
Proof: after the inclusion into the ambient ring, the law is the identity law of `R`.
Subtype extensionality gives equality of the maps. -/
theorem restrictionMap_id (I : RingedSiteIdeal R) (X : Cᵒᵖ) :
    I.restrictionMap (𝟙 X) =
      (ModuleCat.restrictScalarsId' ((siteModuleRings R).obj.map (𝟙 X)).hom
        (congrArg RingCat.Hom.hom ((siteModuleRings R).obj.map_id X))).inv.app _ := by
  sorry

/-- Composition law for restriction on an ideal.
Source: Stacks Project, Modules on Sites (blueprint: def-weil-pbc-ringed-site-ideal).
Proof: include each output into the ambient ring and use the composition law of `R`;
subtype extensionality then proves the displayed equality. -/
theorem restrictionMap_comp (I : RingedSiteIdeal R) {X Y Z : Cᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    I.restrictionMap (f ≫ g) = I.restrictionMap f ≫
      (ModuleCat.restrictScalars ((siteModuleRings R).obj.map f).hom).map
        (I.restrictionMap g) ≫
      (ModuleCat.restrictScalarsComp' ((siteModuleRings R).obj.map f).hom
        ((siteModuleRings R).obj.map g).hom ((siteModuleRings R).obj.map (f ≫ g)).hom
        (congrArg RingCat.Hom.hom ((siteModuleRings R).obj.map_comp f g))).inv.app _ := by
  sorry

/-- The underlying module presheaf of an ideal subsheaf.
Source: Stacks Project, Modules on Sites (blueprint: def-weil-pbc-ringed-site-ideal). -/
noncomputable def modulePresheaf (I : RingedSiteIdeal R) :
    PresheafOfModules.{u} (siteModuleRings R).obj where
  obj X := ModuleCat.of (R.obj.obj X) (I.sections X.unop)
  map f := I.restrictionMap f
  map_id X := I.restrictionMap_id X
  map_comp f g := I.restrictionMap_comp f g

/-- The ideals of sections form a sheaf of modules.
Source: Stacks Project, Modules on Sites (blueprint: def-weil-pbc-ringed-site-ideal).
Proof: glue a matching family in the ambient ring sheaf. The restrictions of the glued
section lie in the ideal on the covering sieve, so `local_mem` puts it in the ideal.
Uniqueness follows from uniqueness of the ambient ring-sheaf gluing. -/
theorem modulePresheaf_isSheaf (I : RingedSiteIdeal R) :
    Presheaf.IsSheaf J I.modulePresheaf.presheaf := by
  sorry

/-- The underlying module sheaf of the ideal, with its actual ideals of sections.
Finite generation is Mathlib's `SheafOfModules.IsFiniteType` applied to this module.
Source: Stacks Project, Modules on Sites (blueprint: def-weil-pbc-ringed-site-ideal). -/
noncomputable def module (I : RingedSiteIdeal R) : SheafOfModules.{u} (siteModuleRings R) where
  val := I.modulePresheaf
  isSheaf := I.modulePresheaf_isSheaf

set_option backward.isDefEq.respectTransparency false in
/-- The sectionwise inclusion of an ideal into the rank-one module.
Source: Stacks Project, Modules on Sites, ideal subsheaves
(blueprint: def-weil-pbc-ringed-site-ideal). -/
noncomputable def inclusionApp (I : RingedSiteIdeal R) (X : Cᵒᵖ) :
    I.module.val.obj X ⟶ (SheafOfModules.unit (siteModuleRings R)).val.obj X :=
  ModuleCat.ofHom
    (X := ModuleCat.of (R.obj.obj X) (I.sections X.unop))
    (Y := ModuleCat.of (R.obj.obj X) (R.obj.obj X))
    (I.sections X.unop).subtype

/-- Naturality of the sectionwise inclusion of an ideal subsheaf.
Source: Stacks Project, Modules on Sites, ideal subsheaves
(blueprint: def-weil-pbc-ringed-site-ideal).
Proof: both composites send an ideal section to its restriction in the ambient ring;
the subtype restriction was defined using precisely the ambient restriction map. -/
theorem inclusionApp_naturality (I : RingedSiteIdeal R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    I.module.val.map f ≫
        (ModuleCat.restrictScalars ((siteModuleRings R).obj.map f).hom).map
          (I.inclusionApp Y) =
      I.inclusionApp X ≫ (SheafOfModules.unit (siteModuleRings R)).val.map f := by
  sorry

/-- The canonical inclusion of the ideal module sheaf into the ring module sheaf.
Source: Stacks Project, Modules on Sites, ideal subsheaves
(blueprint: def-weil-pbc-ringed-site-ideal). -/
noncomputable def inclusion (I : RingedSiteIdeal R) :
    I.module ⟶ SheafOfModules.unit (siteModuleRings R) where
  val := { app := I.inclusionApp, naturality := I.inclusionApp_naturality }

/-- There is a unique ideal subsheaf whose sections locally lie in the ideal generated
by images of sections of `I`.
Source: Stacks Project, Modules on Sites, extension of ideals; Algebraization, Tag 099I
(blueprint: def-weil-pbc-ringed-site-ideal).
Proof: take the local saturation of the sectionwise image-generated ideals. Addition,
negation, and multiplication preserve local membership after intersecting covering sieves.
Restriction uses pullback of covering sieves; the local-membership axiom uses transitivity.
The displayed membership formula determines every ideal of sections and hence the subsheaf
uniquely by proof irrelevance. -/
theorem existsUnique_extension (I : RingedSiteIdeal R) (φ : R ⟶ B) :
    ∃! K : RingedSiteIdeal B,
      ∀ (U : C) (b : B.obj.obj (op U)), b ∈ K.sections U ↔
        ∃ S : Sieve U, S ∈ J U ∧ ∀ (V : C) (g : V ⟶ U), S g →
          B.obj.map g.op b ∈
            Ideal.span (Set.range (fun a : I.sections V => φ.hom.app (op V) a)) := by
  sorry

/-- Extension `I B`, the uniquely determined local saturation of the image-generated ideals.
Source: Stacks Project, Modules on Sites, extension of ideals; Algebraization, Tag 099I
(blueprint: def-weil-pbc-ringed-site-ideal). -/
noncomputable def extension (I : RingedSiteIdeal R) (φ : R ⟶ B) : RingedSiteIdeal B :=
  Classical.choose (existsUnique_extension I φ).exists

/-- The induced map of quotient ring sheaves `R/I → B/I B` is an isomorphism, expressed
by its local kernel and local lifting criterion. This avoids replacing sheaf quotients
by sectionwise quotients: the latter need not be sheaves.
Source: Stacks Project, Modules on Sites, locally bijective sheaf maps; Algebraization,
Tag 099I (blueprint: def-weil-pbc-ringed-site-ideal). -/
def IsQuotientIso (I : RingedSiteIdeal R) (φ : R ⟶ B) : Prop :=
  (∀ (U : C) (a : R.obj.obj (op U)),
    φ.hom.app (op U) a ∈ (I.extension φ).sections U ↔ a ∈ I.sections U) ∧
  (∀ (U : C) (b : B.obj.obj (op U)), ∃ S : Sieve U, S ∈ J U ∧
    ∀ (V : C) (g : V ⟶ U), S g → ∃ a : R.obj.obj (op V),
      B.obj.map g.op b - φ.hom.app (op V) a ∈ (I.extension φ).sections V)

end RingedSiteIdeal
end CategoryTheory
