/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.Paper.P1KummerScalarEndpoints

/-! # Scalar preservation of the specified ordinary Kummer class

Source: Stacks 03PL and 06YY; blueprint Charts, scalar Kummer comparison
(blueprint: lem-sp-p1-kummer-chern-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Scalar transport through normalized endpoints preserves the fixed O(1) specification.
Source: Stacks 03PL and 06YY; blueprint Charts, scalar Kummer comparison
(blueprint: lem-sp-p1-kummer-chern-scalar).

Proof: the unit and line derived-normalization fields say that their adjuncts are
single(unitInsertion) and single(lineInsertion), followed by the inverse restriction
comparison. Naturality of the adjunction, including its shift comparison, thus gives
in Ext the equality unitInsertion followed by restriction of the transported class
= the original class followed by lineInsertion. Forget module scalars and precompose
with the integral constant generator. The constant normalization sends one to one,
so that generator followed by the forgotten insertion is the target generator.
Forgetting after restriction is the same exact functor as directly forgetting.
Consequently the ordinaryFiniteClass of the transported arrow is the image of the
original ordinaryFiniteClass under the cohomology map of the forgotten lineInsertion.
The line normalization at one identifies rootMap followed by this insertion with the
rootMap over B. Apply this identity to the fixed Kummer connecting class of O(1),
using functoriality of Sheaf.H.map and the assumed Chern specification. This proves
the target Chern specification without selecting a cohomology generator. -/
theorem p1KummerChernScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {S : Scheme.{u}} (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (e : P1KummerScalarEndpoints φ N hA hB (ProjectiveLine S))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA S hP c) :
    ordinaryFiniteP1ChernSpec B N hB S hP (e.chernImage c) := by
  sorry

end AlgebraicGeometry.Etale
