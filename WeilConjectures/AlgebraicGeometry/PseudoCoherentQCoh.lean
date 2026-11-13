/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCohDegree

/-! # Quasi-coherent cohomology of pseudo-coherent complexes

## References

* [Stacks, Tag 08E5] (Derived Categories of Schemes), [Stacks, Tag 08EE]
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Every pseudo-coherent object of `D(𝒪_Y)` has quasi-coherent cohomology in every degree.
(Stacks, Tag 08E5) -/
theorem schemeDerivedQCohProperty_of_isPseudoCoherent (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (E : schemeDerivedCategory Y) (hE : IsPseudoCoherent Y E) :
    schemeDerivedQCohProperty Y E := by
  intro n
  exact schemeDerivedQCohProperty_of_isPseudoCoherent_degree Y E hE n

end AlgebraicGeometry.Scheme
