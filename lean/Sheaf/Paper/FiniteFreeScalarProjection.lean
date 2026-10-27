/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K8
-/
module

public import Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions

/-! Scalar compatibility for the specified finite-coefficient operations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open WeilConjectures.FiniteFreeCoefficients
namespace WeilConjectures.FiniteFreeProjectionExchange

/-- Finite-free scalar extension preserves the normalized projection maps on either site.
Source: Stacks 07A4 and 0GL1; blueprint main-20261015, sk-thm-purity-transport,
proof Steps 1 and 3 (blueprint: lem-pur-finite-free-scalar-projection).

Proof: ordinary extension by a finite free module is exact and preserves flat objects.
Use its ordinary balanced tensor isomorphism on K-flat representatives to descend the
normalized tensorator on every scheme. The scalar/pullback comparison is the same
balanced map, so it commutes with tensor and with composition of inverse images.
Transpose the proper projection square under the geometric inverse-image adjunction.
The direct-image comparison is the transpose of scalar extension of its counit; hence
both paths become the same tensor/pullback comparison followed by that counit.
For an open immersion transpose under extension by zero. The unit normalization of
scalarOpen and the open tensor comparison identifies both transposes with ordinary
balancing on the open, and with zero outside it. Finally compose proper projection
with the pushforward of open projection and the inverse-image composition comparison.
Naturality of the tensorator and of the direct-image comparison pastes these squares.
This is exactly projectionMapOfCompactification on both sites, proving the compact
formula as well. No invertibility of the geometric projection map is used. -/
theorem finite_free_scalar_projection {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (_hφ : letI := φ.toAlgebra; Module.Finite A B ∧ Module.Free A B) :
    ∀ pro : Bool, ∃ μ : TensorFamily pro φ,
      (∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
        (M : Sites.D pro A X) (K : Sites.D pro A Y),
        ProperProjectionEquation pro φ μ f M K) ∧
      (∀ {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
        (M : Sites.D pro A X) (K : Sites.D pro A Y),
        OpenProjectionEquation pro φ μ j M K) ∧
      (∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
        (M : Sites.D pro A X) (K : Sites.D pro A Y),
        ProjectionEquation pro φ μ c M K) := by
  sorry

end WeilConjectures.FiniteFreeProjectionExchange
