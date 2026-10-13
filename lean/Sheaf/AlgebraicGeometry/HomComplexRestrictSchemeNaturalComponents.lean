module
public import Sheaf.Algebra.Homology.HomComplexRestrictOpen
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
@[expose] public section
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry
/-- Restriction isomorphisms for ordinary Hom complexes can be chosen
naturally in the second complex.
Source: Stacks Project, Cohomology, Tag 08DL.
(blueprint: lem-sc-hom-complex-restrict-scheme-natural-components)
Proof: choose the componentwise chain isomorphisms induced by restriction of
local module maps. Naturality follows by checking every product projection;
the two composites are restrictions of the same postcomposition map. -/
theorem homComplex_restrict_scheme_natural_components {Y : Scheme.{u}} (U : Y.Opens)
    (L : CochainComplex Y.Modules ℤ) :
    ∃ e : ∀ M : CochainComplex Y.Modules ℤ,
      ((homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj (op L) ⋙
          (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj M ≅
      ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ) ⋙
        (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj
          (op (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj L))).obj M
    , ∀ {M N} (f : M ⟶ N),
      ((homComplexFunctor (R := Y.toRingedSpace.sheaf)).obj (op L) ⋙
          (Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).map f ≫ (e N).hom =
      (e M).hom ≫ ((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ) ⋙
        (homComplexFunctor (R := U.toScheme.toRingedSpace.sheaf)).obj
          (op (((Scheme.Modules.restrictFunctor U.ι).mapHomologicalComplex (.up ℤ)).obj L))).map
          f := by sorry
end AlgebraicGeometry
