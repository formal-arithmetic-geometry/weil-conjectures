module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Triangulated.Functor

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- The termwise tilde functor in the preceding construction is compatible
with the canonical integer shift and is triangulated. This is the final
compatibility step of Stacks Project, Tag 06Z0.
Proof: Exact termwise tilde commutes with translation of complexes, including
the signed differentials, and with mapping cones. Its localization therefore
carries distinguished cone triangles to distinguished triangles and has a
compatible integer-shift structure. Transfer that structure through the
given natural isomorphism after Q. The localization universal property
descends the shift isomorphisms and their coherence to F followed by the
full-subcategory inclusion; it also descends preservation of triangles.
(blueprint: new-affine-qcoh-derived-tilde-triangulated) -/
theorem affineQCohDerivedEquivalence_core_triangulated (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedQCohCategory (Spec (.of A)))
    (h : Nonempty (DerivedCategory.Q ⋙ F ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q)) :
    ∃ (_h : (F ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).CommShift ℤ),
      (F ⋙ (schemeDerivedQCohProperty (Spec (.of A))).ι).IsTriangulated := by
  sorry

end AlgebraicGeometry
