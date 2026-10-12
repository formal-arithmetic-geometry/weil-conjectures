module

public import Sheaf.Topology.RingedModuleSkyscraper
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

@[expose] public section

universe u_complex
open CategoryTheory TopologicalSpace AlgebraicGeometry
namespace SheafOfModules

/-- Stalk recovery for the termwise skyscraper complex.
(blueprint: lem-pc-skyscraper-complex-stalk-recovery)
The neighbourhood colimit defining the stalk is constant at the original module in
 each degree, and the resulting identifications commute with the differentials. -/
theorem skyscraper_complex_stalk_recovery (X : RingedSpace.{u_complex}) (x : X)
    (M : CochainComplex (ModuleCat.{u_complex} (X.presheaf.stalk x)) ℤ) :
    Nonempty (((RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((ringedModuleSkyscraperFunctor X x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≅ M) := by
  sorry

end SheafOfModules
