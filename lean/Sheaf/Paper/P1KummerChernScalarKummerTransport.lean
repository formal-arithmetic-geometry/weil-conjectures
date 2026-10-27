/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.P1KummerChernScalarClassTransport

/-! # Kummer-class normalization after scalar transport

Source: Stacks 03PL and 06YY; blueprint lem-sp-p1-kummer-chern-scalar.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The forgotten normalized line insertion carries the fixed Kummer class over A
 to the fixed Kummer class over B.
Source: Stacks 03PL and 06YY; blueprint lem-sp-p1-kummer-chern-scalar.
Proof: evaluate the insertion on the pure generators, use `line_normalization`,
and apply functoriality of the Kummer connecting class and of `Sheaf.H.map`. -/
theorem p1KummerChernScalar_kummer_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {S : Scheme.{u}} (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (e : P1KummerScalarEndpoints φ N hA hB (ProjectiveLine S)) :
    Sheaf.H.map (p1KummerScalarForgetLineMap e) 2
        (ordinaryFiniteP1KummerClass A N hA S hP) =
      ordinaryFiniteP1KummerClass B N hB S hP := by
  sorry

end AlgebraicGeometry.Etale
