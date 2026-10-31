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

/-- The exceptional diagonal factor preserves graph-normalized adjunction coordinates.
Source: the proof of lem-pur-finite-smooth-gamma-normalization, Steps 1 and 3;
Stacks Tags 0F4Y and 0GKM.
(blueprint: lem-pur-finite-smooth-diagonal-coordinates).

Proof: the graph-normalized proper-support comparison intertwines the specified
compact-support exchange with sum extension's exchange. Transpose that equality under
the two sum adjunctions. The unit-exchange-counit definition of sum exchange and both
triangle identities identify its exceptional mate with the inverse-image compositor.
The rightAdjointUniq coordinates preserve these counits by construction. Evaluate at
the coefficient unit and pull back by the diagonal. Its section compositor cancels
that inverse-image compositor, giving the displayed equality. This argument uses
maps of sheaves and their exact derived functors, so it includes the empty scheme,
open immersions and nonconstant numbers of sheets. -/
theorem finiteSmoothDiagonal_coordinates
    (ell n : ℕ) [Fact ell.Prime] (hn : 1 ≤ n)
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (hX : ∀ x : X, IsUnit (ell : X.presheaf.stalk x))
    (hY : ∀ y : Y, IsUnit (ell : Y.presheaf.stalk y))
    (f : X ⟶ Y) [Etale f] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [HasCompactification f]
    (N : FiniteSmoothCompactSupportComparisons (NoetherianSectionSpecialization.Coeff ell n))
    (hN : FiniteSmoothComparisonNormalized (NoetherianSectionSpecialization.Coeff ell n) N) :
    finiteSmoothDiagonalFactor _ f ≫
        (finiteSmoothSectionCoordinates _ N (pullback.fst f f) (pullback.diagonal f)).hom =
      (finiteSmoothOmegaCoordinates _ N f).hom := by sorry

end AlgebraicGeometry.Etale
