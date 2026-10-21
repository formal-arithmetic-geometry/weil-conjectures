/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.RingedSiteIdeal
public import Sheaf.Paper.RingedTopoiTensorSections
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Colimits

/-! # Ideal products and quotients on a ringed site

Source: Stacks Project, Modules on Sites, Tags 03CY and 03EK.
(blueprint: def-weil-pbc-ideal-module-quotients).
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedSiteIdeal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}

/-- Local membership for a submodule presheaf inside a module sheaf.
Source: Stacks 03CY (blueprint: def-weil-pbc-ideal-module-quotients). -/
def IsSaturated (F : SheafOfModules.{u} (siteModuleRings R)) (N : F.val.Submodule) : Prop :=
  ∀ (U : C) (x : F.val.obj (op U)) (S : Sieve U), S ∈ J U →
    (∀ (V : C) (g : V ⟶ U), S g → F.val.map g.op x ∈ N.obj (op V)) → x ∈ N.obj (op U)

/-- The ideal product is the intersection of all submodule subsheaves containing the
sectionwise ideal multiples. This is a real local-saturation construction.
Source: Stacks 03CY, 03EK (blueprint: def-weil-pbc-ideal-module-quotients). -/
def localProduct (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)) :
    F.val.Submodule :=
  sInf {N | IsSaturated F N ∧ ∀ U : C,
    I.sections U • (⊤ : Submodule (R.obj.obj (op U)) (F.val.obj (op U))) ≤ N.obj (op U)}

/-- The quotient module presheaf, computed sectionwise as a cokernel of the inclusion.
Source: Stacks 03CY (blueprint: def-weil-pbc-ideal-module-quotients). -/
def moduleQuotientPresheaf (I : RingedSiteIdeal R)
    (F : SheafOfModules.{u} (siteModuleRings R)) :
    PresheafOfModules.{u} (siteModuleRings R).obj :=
  cokernel (localProduct I F).ι

/-- Sheafification of the sectionwise quotient by the local ideal product.
Source: Stacks 03CY (blueprint: def-weil-pbc-ideal-module-quotients). -/
def moduleQuotient (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)) :
    SheafOfModules.{u} (siteModuleRings R) :=
  (PresheafOfModules.sheafification (𝟙 (siteModuleRings R).obj)).obj
    (moduleQuotientPresheaf I F)

/-- The actual quotient projection, followed by the module sheafification unit.
Source: Stacks 03CY (blueprint: def-weil-pbc-ideal-module-quotients). -/
def moduleProjection (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)) :
    F ⟶ moduleQuotient I F where
  val := cokernel.π (localProduct I F).ι ≫
    (PresheafOfModules.sheafificationAdjunction (𝟙 (siteModuleRings R).obj)).unit.app
      (moduleQuotientPresheaf I F)

/-- The ring quotient presheaf with its induced restrictions.
Source: Stacks 03CY, 03EK (blueprint: def-weil-pbc-ideal-module-quotients). -/
def ringQuotientPresheaf (I : RingedSiteIdeal R) : Cᵒᵖ ⥤ CommRingCat.{u} where
  obj W := CommRingCat.of (R.obj.obj W ⧸ I.sections W.unop)
  map {W V} f := CommRingCat.ofHom
    (Ideal.quotientMap (I.sections V.unop) (R.obj.map f).hom
      (fun a ha ↦ I.restriction f.unop a ha))
  map_id W := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact congrArg (Ideal.Quotient.mk (I.sections W.unop))
      (congrArg (fun k ↦ k r) (R.obj.map_id W))
  map_comp {W V Z} f g := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext r
    exact congrArg (Ideal.Quotient.mk (I.sections Z.unop))
      (congrArg (fun k ↦ k r) (R.obj.map_comp f g))

/-- Projection to the sectionwise quotient ring presheaf.
Source: Stacks 03CY (blueprint: def-weil-pbc-ideal-module-quotients). -/
def ringQuotientPresheafProjection (I : RingedSiteIdeal R) :
    R.obj ⟶ ringQuotientPresheaf I where
  app W := CommRingCat.ofHom (Ideal.Quotient.mk (I.sections W.unop))
  naturality {W V} f := by ext r; rfl

/-- The quotient ring sheaf is the sheafification, not the sectionwise quotient.
Source: Stacks 03CY (blueprint: def-weil-pbc-ideal-module-quotients). -/
def ringQuotient (I : RingedSiteIdeal R) : Sheaf J CommRingCat.{u} :=
  (presheafToSheaf J CommRingCat).obj (ringQuotientPresheaf I)

/-- The quotient ring-sheaf map.
Source: Stacks 03CY (blueprint: def-weil-pbc-ideal-module-quotients). -/
def ringProjection (I : RingedSiteIdeal R) : R ⟶ ringQuotient I where
  hom := ringQuotientPresheafProjection I ≫ toSheafify J (ringQuotientPresheaf I)

/-- Inclusion of ideal subsheaves, section by section.
Source: Stacks 03EK (blueprint: def-weil-pbc-ideal-module-quotients). -/
def IsContained (I' I : RingedSiteIdeal R) : Prop := ∀ U : C, I'.sections U ≤ I.sections U

/-- The presheaf quotient transition induced by inclusion of ideals.
Source: Stacks 03CY (blueprint: def-weil-pbc-ideal-module-quotients). -/
def ringQuotientPresheafTransition {I' I : RingedSiteIdeal R} (h : IsContained I' I) :
    ringQuotientPresheaf I' ⟶ ringQuotientPresheaf I where
  app W := CommRingCat.ofHom (Ideal.Quotient.factor (h W.unop))
  naturality {W V} f := by
    apply CommRingCat.hom_ext
    apply Ideal.Quotient.ringHom_ext
    ext r
    rfl

/-- Sheafify the sectionwise quotient transition.
Source: Stacks 03CY (blueprint: def-weil-pbc-ideal-module-quotients). -/
def ringTransition {I' I : RingedSiteIdeal R} (h : IsContained I' I) :
    ringQuotient I' ⟶ ringQuotient I :=
  (presheafToSheaf J CommRingCat).map (ringQuotientPresheafTransition h)

/-- The quotient coefficient ring regarded as an R-module sheaf.
Source: Stacks 03EK (blueprint: def-weil-pbc-ideal-module-quotients). -/
def quotientCoefficient (I : RingedSiteIdeal R) : SheafOfModules.{u} (siteModuleRings R) :=
  (SheafOfModules.RingedTensor.restriction (ringProjection I)).obj
    (SheafOfModules.unit (siteModuleRings (ringQuotient I)))

/-- The tensor in the statement is the existing sheaf tensor with the quotient coefficient.
Source: Stacks 03EK (blueprint: def-weil-pbc-ideal-module-quotients). -/
def quotientTensor (I : RingedSiteIdeal R) (F : SheafOfModules.{u} (siteModuleRings R)) :
    SheafOfModules.{u} (siteModuleRings R) :=
  (SheafOfModules.monoidalCategory R).tensorObj F (quotientCoefficient I)

end CategoryTheory.RingedSiteIdeal
