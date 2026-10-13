/- Copyright (c) 2026 The SHEAF contributors. -/
module
public import Sheaf.AlgebraicGeometry.AffinePerfectModuleModel
import Sheaf.AlgebraicGeometry.OpenDerivedRestrictionComparison
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence
import Sheaf.AlgebraicGeometry.AffineLocalizedSiteDerivedTransport
/-! # Affine derived preimages of restricted quasi-coherent targets

Source: Stacks Project, Tag 06Z0, with exact restriction to an affine open.
(blueprint: new-affine-open-supported-model-exists).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
/-- The inverse affine derived equivalence supplies a model of the restricted target.
Source: Stacks Project, Tag 06Z0, and exact open and affine-site transport.
(blueprint: new-affine-open-supported-model-exists).

Proof: The homology shift isomorphism identifies every cohomology sheaf of E'[k]
with one of E', hence it is quasi-coherent. Exact open restriction and the over-site
module equivalence preserve quasi-coherence. Restrict further along the inverse
of the affine chart isoSpec; restriction along an isomorphism is an exact equivalence
and preserves quasi-coherent sheaves, so the result K on Spec A is quasi-coherent.
Use the inverse of the affine derived equivalence on K to obtain M. Its counit,
followed by the canonical affine-site transport, identifies the transported derived
tilde of M with the restriction of E'[k]. The comparisons on module complexes for
this composite and for F give an isomorphism after precomposition with Q. The
universal property of localization lifts that natural isomorphism to D(A).
Its component at M gives the required isomorphism. Support is not used. The same
construction works for the empty affine open and arbitrary, unbounded E'. -/
theorem affine_open_supported_model_exists
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E' : schemeDerivedQCohCategory X)
    (U : X.Opens) (hU : IsAffineOpen U) (k : ℤ)
    [HasDerivedCategory.{u + 1} (ModuleCat.{u} (X.sheaf.obj.obj (op U)))]
    (F : DerivedCategory (ModuleCat.{u} (X.sheaf.obj.obj (op U))) ⥤
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)))
    (hF : Nonempty (DerivedCategory.Q ⋙ F ≅
      (affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q)) :
    ∃ M : DerivedCategory (ModuleCat.{u} (X.sheaf.obj.obj (op U))),
      Nonempty (F.obj M ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
          (E'.obj⟦k⟧)) := by sorry
end AlgebraicGeometry.Scheme
