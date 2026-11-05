/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.AffineBasisSectionsDerivedUnit
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # Affine sections of an unbounded quasi-coherent resolution

Source: Stacks Project, Cohomology, Lemma 08C2, with affine vanishing 01XB.
(blueprint: lem-sc-affine-open-sections-resolution-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The global-ring module presheaf functor is additive.
Source: Stacks Project, 08C2 (blueprint: lem-sc-affine-open-sections-resolution-quasi-iso).
Proof: its maps apply the given module map on each open; addition is componentwise. -/
instance alternatingCechModulePresheaf_additive (X : Scheme.{u}) :
    (alternatingCechModulePresheaf (X := X)).Additive where
  map_add := by
    intro F G f g
    ext V x
    rfl

end AlgebraicGeometry
