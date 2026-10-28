/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.FiniteKummerBoundaryEquation
public import Sheaf.Paper.FiniteP1KummerCoordinates

/-! # The finite ordinary Kummer boundary from the scalar class

Source: diagonal-tower trace (1), the finite positive Kummer class and its site comparison.
(blueprint: lem-sfb-finite-p1-ordinary-kummer-boundary-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/--
The normalized scalar Kummer class of the ordinary projective-line Chern arrow
implies the finite intrinsic boundary equation for the explicitly normalized
coefficient coordinates.  The scalar-class hypothesis is the independent
ordinary etale step; the conclusion is the finite site-comparison step.

Source: diagonal-tower trace (1), comparison with the scalar Kummer class;
Stacks 03PL and 03FD.  The proof transports the class through exact evaluation,
coefficient-coordinate, and scalar-forgetting comparisons.  The normalized
section equations identify the integral and root endpoint maps with
`finiteQuotient` and `finiteRootMap`; naturality of the single and shifted
connecting morphisms then gives the boundary equation.  No tower Chern arrow or
normalization hypothesis occurs in the conclusion.
(blueprint: lem-sfb-finite-p1-ordinary-kummer-boundary-core).
-/
theorem finiteP1_ordinary_kummer_boundary_of_class
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (k : Kummer l X)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (hclass : Etale.ordinaryFiniteP1ChernSpec (FiniteRing l E n) (l ^ (n + 1))
      (ULift.ext _ _ (coefficient_annihilates l E n)) S
      (finiteP1_unitOnPullback (l ^ (n + 1)) (ProjectiveLine S ↘ S)
        (by simpa only [Nat.cast_pow] using hS.pow (n + 1)))
      (geoP1EtaleChern (FiniteRing l E n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _)
        (ULift.ext _ _ (coefficient_annihilates l E n)) S
        (by simpa only [Nat.cast_pow] using hS.pow (n + 1)))) :
    FiniteKummerBoundary l E X n k
      (Scheme.Pic.mapHom e.hom (hyperplanePic S))
      (finiteP1OrdinaryKummerArrow l E n e hS c) := by
  sorry

end AlgebraicGeometry.ProEtale.DiagonalTrace
