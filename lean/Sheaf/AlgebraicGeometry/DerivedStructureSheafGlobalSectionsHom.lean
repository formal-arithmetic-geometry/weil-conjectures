/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # Derived global sections and maps from the structure sheaf
Source: Stacks Project, Tag 09M1, proof, first paragraph.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The structure-sheaf case of the derived global-sections adjunction.
Source: Stacks Project, Tag 09M1, proof of Proposition perfect-proposition-compact-is-perfect,
first paragraph; Tag 0B6A for the K-injective computation of derived global sections.
(blueprint: lem-pc-derived-structure-sheaf-global-sections-hom).
Proof: Represent E by a K-injective complex J of module sheaves. Localization identifies
maps from O_X[0] to E with homotopy classes of chain maps O_X[0] to J. Evaluation at 1
identifies such chain maps with chain maps A[0] to Γ(X,J): in degree zero both are global
cycles, and in degree -1 their homotopies are global sections whose differentials are
the differences of these cycles. These identifications respect addition. Since A is
free of rank one, A[0] is K-projective, so its homotopy classes of maps to Γ(X,J) are
its derived maps to QΓ(X,J). The K-injective computation identifies the latter target
with RΓ(E). For a morphism E to E', take K-injective representatives and lift it to a
chain map using the full faithfulness of localization on K-injectives. Evaluation at 1
commutes with postcomposition and with Γ of that chain map. Homotopic lifts give the
same class. Comparison homotopy equivalences between resolutions give the same maps,
so the resulting equivalences are natural for all derived morphisms. No acyclicity of
Γ(X,J) is required: K-projectivity of A[0] suffices on the module side. -/
theorem derivedStructureSheaf_globalSections_hom (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    letI := HasDerivedCategory.standard
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    let RΓ := (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightDerivedFunctor
    let A₀ := (DerivedCategory.singleFunctor
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) 0).obj
        (ModuleCat.of ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
          ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))
    ∃ e : ∀ E : schemeDerivedCategory X,
      (((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
          (SheafOfModules.unit (moduleRings X.toRingedSpace))) ⟶ E) ≃+
        (A₀ ⟶ RΓ.obj E),
      ∀ (E E' : schemeDerivedCategory X) (f : E ⟶ E') (g :
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit (moduleRings X.toRingedSpace)) ⟶ E),
        e E' (g ≫ f) = e E g ≫ RΓ.map f := by sorry

end AlgebraicGeometry
