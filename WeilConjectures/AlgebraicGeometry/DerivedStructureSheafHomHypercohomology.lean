/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.DerivedStructureSheafGlobalSectionsHom
import WeilConjectures.Algebra.Homology.DerivedFreeModuleHomology

/-! # Hom from the derived structure sheaf
Source: Stacks Project, Tag 09M1, proof of Proposition perfect-proposition-compact-is-perfect,
first paragraph.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option maxHeartbeats 400000 in
-- The sheaf instances and nested derived functors require extra elaboration heartbeats.
-- The sheaf instances and nested derived functors require extra elaboration heartbeats.
/-- Hom from the degree-zero structure sheaf is naturally the zeroth derived global sections.
Source: Stacks Project, Tag 09M1, proof of Proposition perfect-proposition-compact-is-perfect,
first paragraph. -/
theorem derivedStructureSheaf_hom_hypercohomology (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    let F := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) 0 ⋙
      forget₂ (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
    ∃ e : ∀ E : schemeDerivedCategory X,
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace))) ⟶ E) ≃+ F.obj E,
      ∀ (E E' : schemeDerivedCategory X) (f : E ⟶ E') (g :
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings X.toRingedSpace)) ⟶ E),
        e E' (g ≫ f) = F.map f (e E g) := by
  let := HasDerivedCategory.standard
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
  obtain ⟨a, ha⟩ := derivedStructureSheaf_globalSections_hom X
  obtain ⟨b, hb⟩ := derivedFreeModule_hom_homology
    ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
  refine ⟨fun E ↦ (a E).trans (b _), ?_⟩
  intro E E' f g
  change b _ (a E' (g ≫ f)) = _
  rw [ha E E' f g]
  exact hb _ _ _ _

end AlgebraicGeometry
