/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.ResidueField
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative

/-! # A local degree-zero unit criterion for perfect complexes

Source: Stacks Project, Tags 0E62 and 0BCD.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- A map from the structure sheaf in degree zero to a perfect complex is surjective
on degree-zero cohomology at a point if its derived residue map is invertible and the
negative cohomology of that derived fibre vanishes.
Source: Stacks Project, Tag 0E62, local argument, and Tag 0BCD.
(blueprint: lem-sc-perfect-local-degree-zero-unit).

Proof: Choose the affine finite free residue model of Tag 0BCD at s. The negative
terms have rank zero, and the degree-zero term has rank one: the derived fibre map
identifies its degree-zero cohomology with the residue field. In the residue complex,
the term ranks equal the cohomology dimensions, so the differentials are zero.
Represent the given derived map on this affine by a chain map from O[0]; the source
is projective on an affine, so maps into the bounded projective representative are
computed by chain maps. Its degree-zero component reduces to an invertible map of
one-dimensional residue spaces. At the local ring it is multiplication by a unit.
The chain-map equation makes the outgoing differential zero, since its composite
with this invertible component is zero. There is no incoming differential, so the
local degree-zero cohomology is the rank-one term itself. Multiplication by the
inverse unit provides a preimage of every germ. Transport through the representative
isomorphism and the exact stalk functor. Only the fixed fibre is used; no condition
at the other points of the scheme is imposed. -/
theorem surjective_stalk_homology_of_perfect_local_unit (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ U : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    [∀ x : S, HasDerivedCategory.{w} (SheafOfModules.{u}
      (moduleRings (Spec (S.residueField x)).toRingedSpace))]
    (K : schemeDerivedCategory S) (hK : Scheme.IsPerfect S K)
    (a : (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).obj
        (SheafOfModules.unit S.ringCatSheaf) ⟶ K) (s : S)
    (hnegative : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) i).obj
        ((derivedPullback (S.fromSpecResidueField s)).obj K)))
    (ha : IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (S.residueField s)).toRingedSpace)) 0).map
        ((derivedPullback (S.fromSpecResidueField s)).map a))) :
    Function.Surjective (Scheme.Modules.Hom.stalkLinearMap
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map a) s) := by sorry

end AlgebraicGeometry
