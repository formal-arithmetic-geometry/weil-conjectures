/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.HomComplexSingle

/-! # Naturality of the single-source internal Hom comparison

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

/-- The single-source Hom-complex projection is a natural chain isomorphism.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X, product and map formulas.
(blueprint: lem-sc-hom-complex-single-natural).

Proof: Project in degree n onto the factor with source degree zero. All other
factors are zero, so the product universal property gives an inverse. The
single complex has zero differential, so the differential formula identifies
the projection with postcomposition by the target differential. The map formula
for the Hom complex identifies the projection of each mapped chain morphism
with postcomposition by that morphism, proving naturality in every degree. -/
theorem homComplex_single_natural_iso
    (Y : Scheme.{u})
    (P : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    Nonempty ((homComplexFunctor (R := Y.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P)) ≅
      ((SheafOfModules.homFunctor Y.sheaf).obj (op P)).mapHomologicalComplex (.up ℤ)) := by sorry

end AlgebraicGeometry
