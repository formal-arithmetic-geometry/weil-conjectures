module

public import Sheaf.Topology.RingedModuleSkyscraper
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

universe u_complex
open CategoryTheory TopologicalSpace AlgebraicGeometry
namespace SheafOfModules

/-- Acyclicity preservation for termwise skyscraper complexes.
(blueprint: lem-pc-skyscraper-complex-acyclic)
Exactness is checked on sections: opens containing the chosen point reproduce the
original exact sequence, and the other opens give the zero sequence. -/
theorem skyscraper_complex_acyclic (X : RingedSpace.{u_complex}) (x : X)
    (M : CochainComplex (ModuleCat.{u_complex} (X.presheaf.stalk x)) ℤ) :
    M.Acyclic → (((ringedModuleSkyscraperFunctor X x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj M).Acyclic := by
  sorry

end SheafOfModules
