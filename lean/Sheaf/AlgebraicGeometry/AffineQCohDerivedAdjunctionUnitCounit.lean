module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Basic

import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- The affine derived adjunction has invertible unit and counit.
Source: Stacks Project, Tag 06Z0, proof after the elucidation.
(blueprint: new-affine-qcoh-derived-adjunction-unit-counit).

Proof: Global sections is a right adjoint and therefore preserves products;
restriction of scalars through ΓSpecIso is exact and preserves products.
Affine vanishing gives the bound N = 1 on quasi-coherent sheaves.
The same bound holds for underlying abelian groups, and forgetting the
module structure is exact and conservative, so degreewise isomorphisms
can be checked there. The unbounded cohomological bound applied to the
negative truncation, and the truncation triangle, identify degree-zero
cohomology of derived sections with sections of degree-zero cohomology.
Apply this also to every shifted object to obtain the identification in all
degrees. Exactness of tilde identifies the cohomology of F with tilde of
cohomology. Thus the derived counit induces the ordinary counit on each
cohomology sheaf, an isomorphism by quasi-coherence; the derived unit induces
the ordinary module unit, also an isomorphism. Both are quasi-isomorphisms,
hence isomorphisms in the derived categories. The two comparisons transport
this conclusion to F and G. Any adjunction on these functors has invertible
unit and counit, since the adjunction is unique up to an isomorphism of right
adjoints and invertibility is preserved by that isomorphism. -/
theorem affineQCohDerivedAdjunction_unit_counit (A : Type u) [CommRing A]
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
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor)) :
    (∀ M, IsIso (adj.unit.app M)) ∧ (∀ K, IsIso (adj.counit.app K)) := by
  sorry

end AlgebraicGeometry
