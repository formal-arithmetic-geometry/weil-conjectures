/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerCoordinates
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1OrdinaryKummerBoundaryCore

/-! # The integral boundary of the ordinary finite Kummer class
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

/-- The ordinary positive Chern arrow, expressed in the finite coefficient coordinates,
has the integral positive Kummer boundary. No tower Chern construction occurs here.

Source: Stacks 03PL and 03FD. -/
theorem finiteP1_ordinary_kummer_boundary
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (k : Kummer l X)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ)
    [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    FiniteKummerBoundary l E X n k
      (Scheme.Pic.mapHom e.hom (hyperplanePic S))
      (finiteP1OrdinaryKummerArrow l E n e hS c) := by
  apply finiteP1_ordinary_kummer_boundary_of_class l E e k hS n c
  exact (Etale.projectiveLineTraceDatum (l ^ (n + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (FiniteRing l E n)
    (ULift.ext (coefficient_annihilates l E n)) S
    (by simpa only [Nat.cast_pow] using hS.pow (n + 1))).chern_spec

end AlgebraicGeometry.ProEtale.DiagonalTrace
