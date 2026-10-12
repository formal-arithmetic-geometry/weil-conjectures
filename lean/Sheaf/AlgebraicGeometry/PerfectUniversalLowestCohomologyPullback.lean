/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.PerfectJumpLoci

/-! # Pullback of universally free lowest cohomology

Source: Stacks Project, Tag 0BDL.
(blueprint: lem-sc-perfect-universal-lowest-cohomology-pullback).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- Universally free lowest cohomology of a perfect complex commutes with pullback.
This assertion constructs no representing scheme and does not assume a rank-bound open.
Source: Stacks Project, Tag 0BDL, pullback compatibility in the matrix-chart proof.
(blueprint: lem-sc-perfect-universal-lowest-cohomology-pullback).

Proof:
1. Test universal freeness on each residue-field map of `T`. The degree-`a` fibre
   dimension is `r`. Choose the residue model on an affine neighbourhood of its
   image in `S`, using Tag 0BCD. Tor amplitude kills all terms below `a`; the first
   term has rank `r`. Pull this bounded finite-free model to an affine
   neighbourhood in `T`; termwise pullback computes derived pullback.
2. The kernel of its outgoing matrix is locally free of rank `r` by the test with
   the identity of `T`. Locally trivialize it. The square injective inclusion into
   the first free term has cokernel with zero dual (Tag 0EWY), and the coordinate
   maps of the outgoing differential factor through this cokernel. Hence that
   differential is zero. Lowest cohomology is consequently the first free term.
3. Further termwise pullback keeps the differential zero, so both sides of the
   asserted isomorphism are the pullback of that same first free term. Use the
   canonical homology comparison, rather than choosing unrelated trivializations.
   These comparisons agree on overlaps by their naturality, and hence glue to an
   isomorphism of module sheaves on `T'`. -/
theorem perfectUniversalLowestCohomology_pullback
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S) (hE : IsPerfect S E) (a b : ℤ)
    (hamp : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes S E F i)
    (r : ℕ)
    (T : Scheme.{u}) (h : T ⟶ S)
    (hfree :
      ∀ (T' : Scheme.{u}) (u' : T' ⟶ T),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
              ((derivedPullback (u' ≫ h)).obj E)) r)
    (T' : Scheme.{u}) (g : T' ⟶ T) :
    Nonempty
      ((Modules.tensorPullback g).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
              ((derivedPullback h).obj E)) ≅
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
            ((derivedPullback (g ≫ h)).obj E)) := by sorry

end AlgebraicGeometry.Scheme
