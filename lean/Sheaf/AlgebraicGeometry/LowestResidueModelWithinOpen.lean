/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P2
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Sheaf.AlgebraicGeometry.DerivedFiberBetti
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Restricting a residue model to a prescribed open

Source: Stacks Project, Tags 0BDL and 0BCD.
(blueprint: lem-sc-lowest-residue-model-within-open).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A supplied residue model can be restricted inside a prescribed open and has no
terms below the lower Tor bound. This constructs no representing closed subscheme.
Source: Stacks Project, Tag 0BDL, affine model paragraph, and Tag 0BCD.
(blueprint: lem-sc-lowest-residue-model-within-open).

Proof: Tor amplitude implies that the derived residue fibre at U.ι x has zero
cohomology below a: use the stalk tensor criterion for Tor amplitude and tensor
with its residue field. Thus every Betti number in those degrees is zero. In the
supplied model P its term in each such degree is isomorphic to the free sheaf on
the empty indexing type, hence is zero. Choose an affine neighbourhood of U.ι x
inside O intersect U using the affine basis. Regard it as V inside U. Restrict P
to this neighbourhood and transport it from the over-site to V.toScheme by the
module equivalence. Restriction and this equivalence are exact and preserve free
sheaves with the same indexing types, and hence preserve the upper bound and
all prescribed ranks. Their termwise localization comparisons and the exact-open
comparison with derived pullback give the displayed derived isomorphism. The
first rank is the original degree-a Betti number, not a rank at a different point.
No assumption a <= b is necessary; when a > b all fibre ranks vanish. An empty U
has no x to consider, and zero ranks give actual zero free terms. -/
theorem lowestResidueModel_withinOpen
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S : Scheme.{u})
    [∀ O : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over O))]
    (E : schemeDerivedCategory S) (a b : ℤ)
    (hamp : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      ∀ j : ℤ, j < a ∨ b < j → schemeDerivedTensorCohomologyVanishes S E F j)
    (U : S.Opens) (x : U.toScheme) (O : S.Opens)
    (hxO : U.ι x ∈ O) (hO : IsAffineOpen O)
    (P : CochainComplex (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over O)) ℤ)
    (hbounded : ∃ c d : ℤ, ∀ j : ℤ, j < c ∨ d < j → IsZero (P.X j))
    (hrank : ∀ j : ℤ, Nonempty (P.X j ≅ SheafOfModules.free
      (R := (moduleRings S.toRingedSpace).over O)
        (ULift.{u} (Fin (derivedFiberBetti S E j (U.ι x))))))
    (e : (SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) O).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P) :
    ∃ V : U.toScheme.Opens, x ∈ V ∧ IsAffine V.toScheme ∧
      ∃ K : CochainComplex
          (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) ℤ,
        (∃ c : ℤ, ∀ j : ℤ, c < j → IsZero (K.X j)) ∧
        (∀ j : ℤ, j < a → IsZero (K.X j)) ∧
        (∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
          (R := moduleRings V.toScheme.toRingedSpace)
            (ULift.{u} (Fin (derivedFiberBetti S E j (U.ι x)))))) ∧
        Nonempty ((derivedPullback (V.ι ≫ U.ι)).obj E ≅
          DerivedCategory.Q.obj K) := by sorry

end AlgebraicGeometry.Scheme
