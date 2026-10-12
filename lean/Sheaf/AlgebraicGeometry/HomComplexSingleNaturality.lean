/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G3
-/
module

public import Sheaf.Algebra.Homology.HomComplex
public import Sheaf.AlgebraicGeometry.DerivedCategory

/-! # Naturality of the single-source internal Hom comparison

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The single-source Hom comparison is natural in both the sheaf and the complex.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, Hom-complex product
and functoriality formulas. (blueprint: lem-sc-hom-complex-single-naturality)

Proof: For each sheaf P and complex I, project the product defining Hom(P[0],I)
to its degree-zero source factor. All other factors are zero, because P[0]^p
is zero for p different from zero. The inverse is the product lift with this
component and zero elsewhere. The product universal property gives both inverse
identities. The differential formula reduces to postcomposition by d_I, as the
source differential vanishes. Naturality in I follows from the postcomposition
formula for the product projections. For k:Q → P, the precomposition formula for
those same projections identifies Hom(k[0],I) with degreewise internal Hom(k,I).
These arguments apply to unbounded I, zero P or Q, and the empty scheme. -/
theorem homComplex_single_precomposition_iso (Y : Scheme.{u})
    (P Q : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (k : Q ⟶ P)
    [((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op P)).Additive]
    [((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op Q)).Additive] :
    ∃ bP : (homComplexFunctor.{u, u, u, u} (R := Y.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P)) ≅
      ((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op P)).mapHomologicalComplex (.up ℤ),
    ∃ bQ : (homComplexFunctor.{u, u, u, u} (R := Y.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj Q)) ≅
      ((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op Q)).mapHomologicalComplex (.up ℤ),
      ∀ I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      ((homComplexFunctor.{u, u, u, u} (R := Y.sheaf)).map
          ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map k).op).app I ≫ bQ.hom.app I =
        bP.hom.app I ≫
          (NatTrans.mapHomologicalComplex
            ((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).map k.op) (.up ℤ)).app I := by sorry

end AlgebraicGeometry
