/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DegreeZeroFibreSurjective
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes

/-! # Splitting a perfect complex at degree zero near a point

Source: Stacks Project, More on Algebra, Lemma 15.78.2, Tag 0A1U
(blueprint: lem-sc-perfect-cut-complex-degree-zero).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A perfect complex of nonnegative Tor amplitude splits locally at a point where
its degree-zero cohomology maps onto the degree-zero cohomology of its derived fibre.
The first summand is the restricted degree-zero cohomology sheaf in degree zero;
the second is perfect of Tor amplitude in `[1, ∞)`.
Restriction is the exact over-site functor followed by the canonical equivalence
with module sheaves on the open subscheme. Derived-category existence binders
use the shared Mathlib abelian structures, including on all the opens in question.
Source: Stacks Project, Tag 0A1U, i = 0
(blueprint: lem-sc-perfect-cut-complex-degree-zero).

Proof:
1. By lem-sc-perfect-finite-free-residue-model (Tag 0BCD), choose an affine
   neighbourhood of s with a finite-free model whose ranks are the residue-field
   cohomology dimensions. Nonnegative Tor amplitude kills the negative ranks;
   shrink so the model is concentrated in nonnegative degrees.
2. Apply lem-pc-affine-perfect-cut-degree-zero (Tag 0A1U) to the surjective
   degree-zero fibre map. On a principal neighbourhood the complex splits as its
   nonpositive and positive truncations; the latter is perfect of Tor amplitude
   in `[1, ∞)`. Pass from modules to sheaves on this affine neighbourhood.
3. Negative cohomology vanishes, so the nonpositive truncation is the restriction
   of H⁰(K) placed in degree zero. Substitute it in the splitting. -/
theorem exists_perfect_split_degree_zero (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ (U : X.Opens) (V : U.toScheme.Opens),
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (K : schemeDerivedCategory X) (hKq : schemeDerivedQCohProperty X K)
    (hKp : Scheme.IsPerfect X K)
    (hKa : ∀ F : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      ∀ i : ℤ, i < 0 → schemeDerivedTensorCohomologyVanishes X K F i)
    (s : X) (hs : degreeZeroFibreSurjective X K s) :
    ∃ U : X.Opens, s ∈ U ∧ ∃ P : schemeDerivedCategory U.toScheme,
      Scheme.IsPerfect U.toScheme P ∧
      (∀ F : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace),
        ∀ i : ℤ, i < 1 → schemeDerivedTensorCohomologyVanishes U.toScheme P F i) ∧
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Scheme.Modules.overEquiv U)).mapDerivedCategory.obj K ≅
          (DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).obj
              (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
                Equivalence.functor
                  (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
                  (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
                  (Scheme.Modules.overEquiv U)).obj
                    ((DerivedCategory.homologyFunctor
                      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj K)) ⊞ P) := by
  sorry

end AlgebraicGeometry
