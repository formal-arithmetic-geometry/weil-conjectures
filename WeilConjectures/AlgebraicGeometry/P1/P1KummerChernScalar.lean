/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.P1.P1KummerScalarEndpoints
import WeilConjectures.AlgebraicGeometry.P1.P1KummerChernScalarKummerTransport

/-! # Scalar preservation of the specified ordinary Kummer class

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: the Kummer classes over B are images
of those over A (blueprint: lem-sp-p1-kummer-chern-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Scalar extension preserves the specified ordinary projective-line Kummer class.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: the Kummer classes over B are images
of those over A (blueprint: lem-sp-p1-kummer-chern-scalar).

Proof steps:
1. Transpose the defining conjugate of `c` under the scalar adjunction. Naturality,
including its shift comparison, gives the Ext equality: `mk0(unitInsertion)` composed with
restriction of the transported Ext class equals the original Ext class composed with
`mk0(lineInsertion)`. The two derived-normalization fields `e.unit_derived` and
`e.line_derived` identify the adjuncts used here.
2. Forget scalars and precompose with the integral constant generator. The unit
normalization sends one to one, so the generator followed by the forgotten insertion is
the target generator. The exact functor that forgets after restriction equals direct
forgetting; exact-functor composition compatibility compares their Ext maps. Hence
`ordinaryFiniteClass` of the transported arrow is the cohomology image of the original
`ordinaryFiniteClass` (`p1KummerChernScalar_class_transport`,
blueprint: lem-sp-p1-kummer-chern-class-transport).
3. The root normalization at coefficient one gives `rootMap_A` followed by the forgotten
`lineInsertion` equals `rootMap_B`. Apply functoriality of `H^2` to the fixed Kummer
connecting class of `O(1)` (`p1KummerChernScalar_kummer_transport`,
blueprint: lem-sp-p1-kummer-chern-kummer-transport) and substitute the assumed Chern
specification `hc`. This proves the target specification.
-/
theorem p1KummerChernScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {S : Scheme.{u}} (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (e : P1KummerScalarEndpoints φ N hA hB (ProjectiveLine S))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA S hP c) :
    ordinaryFiniteP1ChernSpec B N hB S hP (e.chernImage c) := by
  unfold ordinaryFiniteP1ChernSpec at hc ⊢
  rw [p1KummerChernScalar_class_transport e c, hc,
    p1KummerChernScalar_kummer_transport hP e]

end AlgebraicGeometry.Etale
