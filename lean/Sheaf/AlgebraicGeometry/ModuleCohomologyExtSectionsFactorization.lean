/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleCohomologyExtResolutionNaturality

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

/-- The fixed module-to-Ext comparison factors through abelian derived sections.
Source: Stacks Project, Tags 015E and 03FD; the Ext-to-sections half of the defining
composite in ModuleCohomologyExtResolutionNaturality.
(blueprint: new-module-cohomology-ext-sections-factorization)

Proof: Unfold moduleCohomologyExtResolutionEquiv and the F-component of
moduleCohomologyExtResolutionNatIso. Its first factor is resolutionSectionsNatIso.
Its second factor is inverse siteSectionsNatIso, the identity siteExtNatIso,
inverse Ext precomposition by terminalSourceIso, and the identity siteHNatIso.
Evaluate the additive equivalence at x. The identity factors disappear, and the
remaining inverse factors are the inverse of terminal-source precomposition
followed by siteSectionsObjIso. This proves the formula without evaluating the
acyclic-resolution comparison inside the first factor, or using a supplied
module resolution. The calculation applies in every degree, including zero,
for zero coefficients and empty schemes. -/
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
          (fun M _ ↦ forgottenInjectiveAcyclic X M)).app F).hom x))) := by sorry

end AlgebraicGeometry.Scheme.Modules.ExtEdgeResolution
