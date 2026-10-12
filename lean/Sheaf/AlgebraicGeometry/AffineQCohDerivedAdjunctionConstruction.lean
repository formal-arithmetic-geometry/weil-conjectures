module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Basic

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- Derived affine tilde and derived global sections admit an adjunction on
quasi-coherent derived objects, with the two defining functor comparisons.
Source: Stacks Project, Tag 06Z0, elucidation of the two adjoint functors;
Tag 079W supplies derived adjunction.
(blueprint: new-affine-qcoh-derived-adjunction-construction).

Proof: View Spec A as a ringed space over the one-point ringed space A.
The pullback is associated sheaf and is exact, since localization of modules
is exact. Apply it termwise to complexes; its cohomology is associated sheaf
of module cohomology, hence quasi-coherent. Localize this complex functor to
obtain F and its comparison. The right adjoint is derived global sections,
computed on K-injective resolutions, with scalars transported through ΓSpecIso.
The ordinary tilde/global-sections adjunction induces the derived adjunction.
Its restriction has the same hom-equivalence because the quasi-coherent
subcategory is full; this gives F ⊣ G and the comparison for G. -/
theorem affineQCohDerivedAdjunction_construction (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))] :
    ∃ (F : DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedQCohCategory (Spec (.of A)))
      (G : schemeDerivedQCohCategory (Spec (.of A)) ⥤ DerivedCategory (ModuleCat.{u} A)),
      Nonempty (F ⊣ G) ∧
      Nonempty (DerivedCategory.Q ⋙ F ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q) ∧
      Nonempty (G ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor) := by
  sorry

end AlgebraicGeometry
