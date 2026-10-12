/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.RingedSpaceModuleCohomology
import Sheaf.AlgebraicGeometry.ModuleAbelianZariskiCohomology
import Sheaf.Paper.PQFCohomology

/-! # Cohomology of a Zariski module and its underlying abelian sheaf

Source: Stacks Project, `sites-cohomology.tex`, Lemma Tag 03FD
(blueprint: lem-sc-zariski-module-abelian-cohomology-agree).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

namespace AlgebraicGeometry

/-- For a scheme and an `𝒪_X`-module, module cohomology agrees canonically and naturally
with cohomology of the underlying abelian sheaf on the small Zariski site.

Source: Stacks Project, `sites-cohomology.tex`, Lemma Tag 03FD
(blueprint: lem-sc-zariski-module-abelian-cohomology-agree).

Proof: apply `lem-sc-module-abelian-zariski-cohomology` to obtain the comparison in every
positive degree. In degree zero, both right derived functors are global sections by
`pqf-def-cohomology` and `def-sc-zariski-cohomology`; choose the identity on sections.
The comparison is natural in the module by the naturality in the cited comparison and by
functoriality of global sections in degree zero.

The last equality spells out the degree-zero identity: send a section through the
canonical map `Γ → R⁰Γ`, then through `e 0`; identify `Ext⁰` with morphisms from the
sheafified free abelian representable, precompose with the sheafification unit, and
evaluate at the generator given by the identity of the top open. The resulting section
must be the original section. Enough injectives for abelian sheaves is supplied by the
Grothendieck structure of sheaves on the small Zariski site, rather than assumed. -/
theorem zariskiModuleAbelianCohomologyAgree (X : Scheme.{u}) :
    ∃ e : ∀ q : ℕ,
      (RingedSpace.moduleCohomology X.toRingedSpace q ⋙
        forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
          AddCommGrpCat.{u}) ≅
      (SheafOfModules.toSheaf (moduleRings X.toRingedSpace) ⋙
        @CategoryTheory.Sheaf.cohomologyPresheafFunctor.{u, u, u}
          (Opens X.carrier) inferInstance (Opens.grothendieckTopology X.carrier)
          inferInstance
          (@hasExt_of_enoughInjectives _ _ _ inferInstance
            (@IsGrothendieckAbelian.enoughInjectives _ _ _
              (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
                (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))) q ⋙
        (evaluation (Opens X.carrier)ᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)),
      ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (s : (RingedSpace.globalSectionsFunctor X.toRingedSpace).obj M),
        ((toSheafify (Opens.grothendieckTopology X.carrier)
              (yoneda.obj (⊤ : Opens X.carrier) ⋙ AddCommGrpCat.free) ≫
            (@Abelian.Ext.addEquiv₀ _ _ _
              (@hasExt_of_enoughInjectives _ _ _ inferInstance
                (@IsGrothendieckAbelian.enoughInjectives _ _ _
                  (Sheaf.isGrothendieckAbelian_of_essentiallySmall'.{u}
                    (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}))) _ _
              ((e 0).hom.app M
                ((forget₂
                    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
                    AddCommGrpCat.{u}).map
                  ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app M)
                  s))).hom).app (op ⊤))
          (FreeAbelianGroup.of (𝟙 (⊤ : Opens X.carrier))) = s := by
  sorry

end AlgebraicGeometry
