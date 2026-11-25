/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.RingedModuleSkyscraper
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.Topology.SkyscraperComplexStalk
import WeilConjectures.Topology.SkyscraperComplexAcyclic

/-!
# Skyscraper complexes and stalks

The termwise skyscraper of a complex of stalk modules recovers that complex on taking stalks,
and carries acyclic complexes to acyclic complexes of sheaves.

## References

* [Stacks Project, Tags 009A and 009C](https://stacks.math.columbia.edu/tag/009C)
-/

@[expose] public section

universe u_complex

open CategoryTheory TopologicalSpace AlgebraicGeometry

namespace SheafOfModules

/-- The termwise skyscraper of a complex of stalk modules recovers that complex on taking
its stalk at the same point, and carries acyclic complexes to acyclic sheaf complexes. -/
theorem skyscraper_complex (X : RingedSpace.{u_complex}) (x : X)
    (M : CochainComplex (ModuleCat.{u_complex} (X.presheaf.stalk x)) ℤ) :
    Nonempty (((RingedSpace.moduleStalkFunctor X x).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
        (((ringedModuleSkyscraperFunctor X x).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M) ≅ M) ∧
      (M.Acyclic → (((ringedModuleSkyscraperFunctor X x).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj M).Acyclic) := by
  exact ⟨skyscraper_complex_stalk_recovery X x M,
    skyscraper_complex_acyclic X x M⟩

end SheafOfModules
