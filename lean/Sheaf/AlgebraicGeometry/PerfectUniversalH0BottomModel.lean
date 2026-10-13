/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Bottom models on a universally free degree-zero locus

Source: Stacks Project, Tags 0BDL, 0BCD and 0EWY.
(blueprint: lem-sc-perfect-universal-h0-bottom-model).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A perfect complex with universally vanishing negative cohomology and locally
universally free degree-zero cohomology has an affine strictly perfect bottom model.
Source: Stacks Project, Tag 0BDL, matrix-chart proof; Tags 0BCD and 0EWY.
(blueprint: lem-sc-perfect-universal-h0-bottom-model).

Proof: Choose the universally rank-r neighbourhood of s and test the hypotheses
at Spec kappa(s). Tag 0BCD gives a bounded finite-free model with ranks the fibre
cohomology dimensions. Shrink its affine neighbourhood inside the chosen open.
The negative ranks are zero and the degree-zero rank is r. Exact restriction
and its comparison with derived pullback identify the kernel of d0 with H0(K)
on this chart. The identity test makes that kernel locally free of rank r.
Trivialize it after a further affine shrinking. Its inclusion into the free
rank-r degree-zero term is an injective square matrix. Tag 0EWY says that its
transpose is injective, so the dual of its cokernel vanishes. Each coordinate
of d0 factors through this cokernel and therefore is zero. This proves d0=0
without a reducedness hypothesis. Restricting the model preserves boundedness
and finite freeness and gives the required derived isomorphism. At rank zero
the degree-zero term and differential are zero. There are no points to treat
on an empty scheme. No source module or arrow is part of this assertion. -/
theorem perfect_universalH0_bottom_model
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (K : schemeDerivedCategory S) (hK : IsPerfect S K)
    (hnegative : ∀ (Y : Scheme.{u}) (k : Y ⟶ S) (i : ℤ), i < 0 →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) i).obj
          ((derivedPullback k).obj K)))
    (hloc : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ r : ℕ,
      ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((derivedPullback (k ≫ U.ι)).obj K)) r)
    (s : S) :
    ∃ U : S.Opens, s ∈ U ∧ IsAffineOpen U ∧
      ∃ B : CochainComplex
          (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U)) ℤ,
        IsStrictlyPerfect S U B ∧
        (∀ i : ℤ, i < 0 → IsZero (B.X i)) ∧ B.d 0 1 = 0 ∧
        Nonempty ((SheafOfModules.overFunctor.{u}
          (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
            DerivedCategory.Q.obj B) := by sorry

end AlgebraicGeometry.Scheme
