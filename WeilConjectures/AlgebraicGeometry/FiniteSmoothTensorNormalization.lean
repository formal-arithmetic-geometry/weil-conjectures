/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothGammaConstructions

/-! # A constituent of finite smooth normalization -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor

noncomputable section

namespace AlgebraicGeometry.Etale

/-- The canonical tensor mate at the sum-adjunction orientation is the inverse
right-adjoint comparison, for every unbounded complex.
Source: the proof of lem-pur-finite-smooth-gamma-normalization, Steps 8--9;
Stacks Tags 0GKF and 0GL5, specified projection compatibility.
(blueprint: lem-pur-finite-smooth-tensor-coordinates).

Proof: transport the specified compact-support projection through the graph-normalized
sum comparison. On a sheet generator its inverse sends (s,m) tensor k to
(s,m tensor s^*k). The signed symmetry used to order the two tensor factors has
sign one when the coefficient unit is in degree zero. Exact sum extension preserves
flat and K-flat complexes, so the same formula computes the projection for all
unbounded K. Under right-adjoint uniqueness, the defining transpose of the smooth
tensor map is tensoring with the sum counit and then evaluating. Precompose with
the inverse unit orientation finiteSmoothOmegaCoordinates: on each sheet this
is evaluation itself. The adjunction Hom bijection therefore identifies this map
with finiteSmoothAdjointCoordinates inverse. The argument also covers K=0, the
empty scheme, the identity morphism and finite disjoint unions. -/
theorem finiteSmoothTensor_coordinates
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (N : FiniteSmoothCompactSupportComparisons (NoetherianSectionSpecialization.Coeff ell n))
    (hN : FiniteSmoothComparisonNormalized (NoetherianSectionSpecialization.Coeff ell n) N) :
    ∀ K : DerivedCategoryModule (NoetherianSectionSpecialization.Coeff ell n) Y,
      finiteSmoothGammaMap _ f (finiteSmoothOmegaCoordinates _ N f) K =
        (finiteSmoothAdjointCoordinates _ N f).inv.app K := by sorry

end AlgebraicGeometry.Etale
