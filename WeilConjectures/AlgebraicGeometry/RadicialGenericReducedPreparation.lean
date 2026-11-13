/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

import WeilConjectures.AlgebraicGeometry.RadicialPreparationConstruction
import WeilConjectures.AlgebraicGeometry.RadicialPreparationFibreComparison

/-! # Radicial preparation before the final generic-flat shrinking

## References

* [Stacks Project, Tag 0559](https://stacks.math.columbia.edu/tag/0559)
* [Stacks Project, Tag 051T](https://stacks.math.columbia.edu/tag/051T)
* [Stacks Project, Tag 052A](https://stacks.math.columbia.edu/tag/052A)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- Construct an affine radicial model with reduced source and geometrically reduced
 generic fibre; flatness and finite presentation are deferred to a subsequent shrinking. -/
theorem exists_radicial_generic_reduced_preparation
    {X T : Scheme.{u}} [IsAffine X] (f : X ⟶ T) [LocallyOfFiniteType f]
    (V : T.Opens) (hV : IsAffineOpen V) (himage : Set.range f ⊆ V)
    (η : T) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (f.fiberToSpecResidueField η)) :
    ∃ (U : T.Opens), η ∈ U ∧ IsAffineOpen U ∧
      ∃ (S Y : Scheme.{u}) (q : S ⟶ U.toScheme) (g : Y ⟶ S),
        IsAffine S ∧ IsIntegral S ∧ IsAffine Y ∧ IsReduced Y ∧
        IsUniversalHomeomorphism q ∧ LocallyOfFiniteType g ∧
        ∃ η' : S, IsGenericPoint η' Set.univ ∧ (q ≫ U.ι) η' = η ∧
          GeometricallyReduced (g.fiberToSpecResidueField η') ∧
          ∀ s : S, GeometricallyIrreducible (g.fiberToSpecResidueField s) ↔
            GeometricallyIrreducible (f.fiberToSpecResidueField ((q ≫ U.ι) s)) := by
  obtain ⟨U, hηU, hUa, S, Y, q, g, hSa, hSi, hYa, hYr, hq, hfg, η', hη', hqη', hred, h, hh, hg⟩ :=
    exists_radicial_preparation_construction f V hV himage η hη hgeom
  have : IsUniversalHomeomorphism h := hh
  have hcmp (s : S) := exists_radicial_preparation_fibre_comparison f (q ≫ U.ι) h s
  rw [hg] at hcmp
  exact ⟨U, hηU, hUa, S, Y, q, g, hSa, hSi, hYa, hYr, hq, hfg,
    η', hη', hqη', hred, hcmp⟩

end AlgebraicGeometry
