module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Sheaf.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Adjunction.Basic

import Sheaf.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech
import Sheaf.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound

/-! # The derived affine counit on cohomology

Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5.
(blueprint: new-affine-derived-counit-homology-factorization).
-/

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- On cohomology the derived affine counit is the ordinary tilde-sections counit,
after identifying its source with associated sheaf of sections of cohomology.
Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5, counit calculation.
(blueprint: new-affine-derived-counit-homology-factorization).

Proof: Global sections, being right adjoint, preserves products; transport of scalars
through ΓSpecIso is exact and preserves products. Affine vanishing gives the bound
N = 1 on quasi-coherent sheaves. The same holds after forgetting to abelian groups,
an exact conservative functor. Apply the unbounded cohomological bound to the negative
truncation and use its truncation triangle to identify degree-zero derived sections
with ordinary sections of degree-zero cohomology. Shifts give this comparison in every
degree. Exact associated sheaf commutes with cohomology. For the adjunction induced
from ordinary tilde and sections, these comparisons identify the derived counit with
the ordinary counit: on a K-injective representative this is the evaluation map,
and the truncation comparisons are natural for that map. For the functors F and G
of the statement, descend the given comparison for F through Q and use the comparison
for G. Uniqueness of right adjoints supplies an isomorphism between the transported
canonical adjunction and adj; absorb its image on cohomology into the source comparison.
The target remains the same cohomology sheaf, giving exactly the displayed equation.
No boundedness of K is assumed: the uniform bound and products are what justify the
negative-truncation passage. The zero object and the zero ring give the zero-map
identity between zero objects, so neither is excluded.
-/
theorem affineDerivedCounit_homology_factorization (A : Type u) [CommRing A]
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
    (K : schemeDerivedQCohCategory (Spec (.of A))) (n : ℤ) :
    ∃ e : (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj
          ((F.obj (G.obj K)).obj) ≅
        (tilde.functor (.of A)).obj ((moduleSpecΓFunctor (R := .of A)).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj K.obj)),
      (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).map
          ((schemeDerivedQCohProperty (Spec (.of A))).ι.map (adj.counit.app K)) =
        e.hom ≫ Scheme.Modules.fromTildeΓ (R := .of A)
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n).obj K.obj) := by
  sorry

end AlgebraicGeometry
