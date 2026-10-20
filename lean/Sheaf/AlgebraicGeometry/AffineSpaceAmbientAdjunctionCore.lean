/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.Compactification.Affine
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! A compactification-specific form of the affine-space ambient adjunction.

Source: blueprint `cor-amb-affine-space-adjunction`.
(blueprint: cor-amb-affine-space-adjunction-compactification-core).

This is the geometric core: the compact-support functor attached to an explicitly chosen
compactification of affine space is left adjoint to the finite torsion Tate-twist pullback.
The final theorem transports this adjunction to the project-wide compactification-independent
`rightDerivedLowerShriek`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Compactification-specific affine-space ambient adjunction.

Proof source: the affine-line/projective-line induction in
`cor-amb-affine-space-adjunction`, with the standard projective compactification supplied by
`Compactification.ofIsImmersionAffineSpace`. The induction composes the normalized
projective-line adjunction along the coordinate tower, identifies the resulting right functor
with the explicit finite Tate-twist pullback and even shift, and transports along the chosen
compactification comparison. This theorem is a strict sub-result of the compactification-
independent assertion below.
(blueprint: cor-amb-affine-space-adjunction-compactification-core). -/
theorem affineSpaceAmbientAdjunction_of_compactification
    (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (c : Compactification (AffineSpace (ULift.{u} (Fin d)) S ↘ S)) :
    Nonempty
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⊣
        ((upperStar (ModuleCat.{u + 1} A)
            (AffineSpace (ULift.{u} (Fin d)) S ↘ S)).mapDerivedCategory ⋙
          derivedTensorRight (ModuleCat.{u + 1} A) (AffineSpace (ULift.{u} (Fin d)) S)
            ((DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateTwist (AffineSpace (ULift.{u} (Fin d)) S) N A hA d))) ⋙
          shiftFunctor _ (2 * (d : ℤ))) := by
  sorry

end AlgebraicGeometry.Etale
