/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality


public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturalityExtension

/-! # The Ext-to-abelian-sections part of the comparison

Source: Stacks Project, Tags 015E and 03FD.
(blueprint: new-module-cohomology-ext-sections-factorization)
-/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem sectionsComparisonNatIso_apply
    {A E : Type*} [Category A] [Category E]
    {R : Type u} [Ring R] {K : A ⥤ ModuleCat.{u} R} {T : A ⥤ E}
    {B L Q : E ⥤ AddCommGrpCat.{u}}
    (a : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ B)
    (b : L ≅ B) (c : L ≅ Q) (F : A) (x : K.obj F) :
    moduleComparisonEquiv (sectionsComparisonNatIso a b c) F x =
      (c.hom.app (T.obj F)) ((b.inv.app (T.obj F)) ((a.hom.app F) x)) := by
  rfl

private theorem sectionsComparisonNatIso_apply_of_eq
    {A E : Type*} [Category A] [Category E]
    {R : Type u} [Ring R] {K : A ⥤ ModuleCat.{u} R} {T : A ⥤ E}
    {B L Q : E ⥤ AddCommGrpCat.{u}}
    (a : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ B)
    (b : L ≅ B) (c : L ≅ Q)
    (η : K ⋙ forget₂ _ AddCommGrpCat.{u} ≅ T ⋙ Q)
    (hη : η = sectionsComparisonNatIso a b c) (F : A) (x : K.obj F) :
    moduleComparisonEquiv η F x =
      (c.hom.app (T.obj F)) ((b.inv.app (T.obj F)) ((a.hom.app F) x)) := by
  subst η
  exact sectionsComparisonNatIso_apply a b c F x

set_option maxHeartbeats 800000 in
-- Elaborating the specialized derived-functor types needs additional instance conversions.
/-- The fixed module-to-Ext comparison factors through abelian derived sections.
Source: Stacks Project, Tags 015E and 03FD; the Ext-to-sections half of the defining
composite in ModuleCohomologyExtResolutionNaturality.
(blueprint: new-module-cohomology-ext-sections-factorization)

Proof: Unfold the fixed comparison and its natural isomorphism. Its constructor
composes the common-resolution section comparison, the inverse site-section
comparison, and the terminal Ext-source comparison. First evaluate this three-map
composite for arbitrary functors, before specializing to the scheme. Apply that
component formula and unfold the definition of module cohomology and the Ext-valued
cohomology type. The inverse site component is siteSectionsObjIso.inv, and the
terminal component is precompAddEquiv.symm. Their composite gives the asserted
formula. This never unfolds the acyclic-resolution comparison inside the first
factor, and includes degree zero, zero coefficients and empty schemes. -/
theorem ext_sections_factorization
    (X : Scheme.{u}) (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (p : ℕ)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace p).obj F) :
    moduleCohomologyExtResolutionEquiv X F p x = (by
      letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
        (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
      let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
      let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
      let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
      let V := forget₂ (ModuleCat.{u}
        ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
      let d := siteSectionsObjIso (Opens.grothendieckTopology X) ⊤ (T.obj F) p
      exact (Abelian.Ext.precompAddEquiv (terminalSourceIso X) (T.obj F) p).symm
        (d.inv (((resolutionSectionsNatIso G V T Γ p (sectionHomologyIso X p)
          (fun M _ ↦ forgottenInjectiveAcyclic X M)).app F).hom x))) := by
  letI : EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let T := SheafOfModules.toSheaf (moduleRings X.toRingedSpace)
  let Γ := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  let G := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let V := forget₂ (ModuleCat.{u}
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat.{u}
  -- Compare natural isomorphisms before evaluating their components.
  unfold moduleCohomologyExtResolutionEquiv
  refine sectionsComparisonNatIso_apply_of_eq
    (K := RingedSpace.moduleCohomology X.toRingedSpace p)
    (resolutionSectionsNatIso G V T Γ p (sectionHomologyIso X p)
      (fun M _ ↦ forgottenInjectiveAcyclic X M))
    (siteSectionsNatIso (Opens.grothendieckTopology X) ⊤ p)
    (extSourceNatIso (terminalSourceIso X) p)
    (moduleCohomologyExtResolutionNatIso X p) ?_ F x
  unfold moduleCohomologyExtResolutionNatIso
  rfl

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
