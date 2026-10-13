/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H2
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.CompletedMatchingRingMap

/-! # Surjectiveity of completed matching sections

Source: Stacks Project, Tags 0BLH, 05ER and 05EU.
(blueprint: lem-sbc-completed-matching-ring-map-surjective)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.CompletionGluingData

/-- The completed matching-ring comparison is surjective.
Source: Stacks Project, Tag 05ER, cokernel argument; Tags 0BLH and 05EU.
(blueprint: lem-sbc-completed-matching-ring-map-surjective)

Proof in words: Choose finitely many generators f_i of the maximal ideal.
Their principal opens cover U
by hU. The finite affine charts of q give B_i, and finite s gives B' = Γ(E).
The overlap isomorphism and the transition maps yield the gluing object of
Tag 05ER. The sheaf equalizer identifies its H⁰ with matchingRing. Completion
is flat and is an isomorphism modulo the maximal ideal. In the proof of 05ER,
the localized comparison is invertible, and its cokernel is (Q,0,0,0), with
Q maximal-ideal-power torsion. Lemma 15.91.8 lifts the extension of Q by
H⁰ tensor_A C to an extension of Q by H⁰ over A. The resulting module has
canonical gluing object equal to the given one. Applying H⁰ and its canonical
identification forces Q = 0. Therefore H⁰ tensor_A C → B' is surjective.
By Tag 05EU this map is the algebra map completedRingMap, characterized by
the second projection and the C-structure. For empty U, A is Artinian and
complete and the comparison is the identity; zero algebras satisfy the same
cokernel argument. -/
theorem completedRingMap_surjective
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {U : (Spec (.of A)).Opens}
    (hU : ∀ x : Spec (.of A), x ∈ U ↔ x ≠ IsLocalRing.closedPoint A)
    {Y : Scheme.{u}} {q : Y ⟶ U.toScheme} [IsFinite q]
    {E : Scheme.{u}} {s : E ⟶ Spec
      (.of (AdicCompletion (IsLocalRing.maximalIdeal A) A))} [IsFinite s]
    (D : CompletionGluingData A U q E s) :
    Function.Surjective D.completedRingMap := by sorry

end AlgebraicGeometry.Scheme.CompletionGluingData
