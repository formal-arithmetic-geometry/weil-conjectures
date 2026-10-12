module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Basic

import Sheaf.AlgebraicGeometry.AffineDerivedSectionsHomologyComparison

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- The affine derived unit induces an isomorphism on every cohomology object.
Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5, module-unit calculation.
(blueprint: new-affine-derived-unit-homology-isIso).

Proof: Use the natural cohomology comparison for derived global sections and the
natural comparison for the derived associated-sheaf functor. Naturality of the
right-derived-functor unit identifies the map induced by the adjunction unit on
cohomology with the ordinary module unit followed by the map induced by a
K-injective quasi-isomorphism. The ordinary affine tilde unit is invertible by
full faithfulness of tilde, and the latter map is invertible because the
resolution is a quasi-isomorphism. Transporting these isomorphisms through the
comparisons and through the given isomorphisms hF and hG proves the claim for
the displayed adjunction. The argument is uniform in the integer degree and
includes the zero ring and zero complex.
-/
theorem affineDerivedUnit_homology_isIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (F : DerivedCategory (ModuleCat.{u} A) ⥤ schemeDerivedQCohCategory (Spec (.of A)))
    (G : schemeDerivedQCohCategory (Spec (.of A)) ⥤ DerivedCategory (ModuleCat.{u} A))
    (adj : F ⊣ G)
    (hF : Nonempty (DerivedCategory.Q ⋙ F ⋙
        (schemeDerivedQCohProperty (Spec (.of A))).ι ≅
        @Functor.mapHomologicalComplex _ _ _ _ _ _ _
          (@id (ModuleCat.{u} A ⥤
            SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ) ⋙
          DerivedCategory.Q))
    (hG : Nonempty (G ≅ (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor))
    (M : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      (adj.unit.app M)) := by
  sorry

end AlgebraicGeometry
