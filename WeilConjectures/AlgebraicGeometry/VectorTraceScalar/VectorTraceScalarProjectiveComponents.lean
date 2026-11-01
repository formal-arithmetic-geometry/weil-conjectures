/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData

/-! # Normalized scalar squares for the two projective-line columns

Source: blueprint/latest, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2.
(blueprint: lem-pur-vector-scalar-projective-components).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The normalized scalar maps preserve separately the twisted unit and the Kummer
column. No affine trace or vector integration is asserted.
Source: vector-bundle-purity proof paragraph 2; scalar-descent proof Steps 1--3.
Proof: the generator equation for normalized balancing is preserved by inverse image.
On the flat Tate line the derived scalar/single map is ordinary balancing, and shifts
preserve this equation. The Kummer scalar theorem identifies the two normalized Chern
maps. Transpose under the actual inverse-image/direct-image adjunction. Naturality of
scalarPullbackIso and the counit-transpose formula for scalarMate reduce the second
column to that Kummer equation. For the first column the same calculation reduces to
the adjunction triangle identity, followed by pullback compatibility of balancing.
Adjunction injectivity gives both displayed equations. The argument uses pure tensor
generators, so it includes nonflat coefficient maps, zero rings, N=1 and empty schemes.
(blueprint: lem-pur-vector-scalar-projective-components). -/
theorem projective_components (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    ((scalarExtension φ S).map
        (ordinaryFiniteP1Unit A N hA (projectiveLineTraceTransport N hN A hA) S hS) ≫
      projective φ N hN hA hB S hS =
      line φ N hN hA hB S hS ≫
        ordinaryFiniteP1Unit B N hB (projectiveLineTraceTransport N hN B hB) S hS) ∧
    ((scalarExtension φ S).map (ordinaryFiniteP1ChernPushforward A N hA S
        (projectiveLineTraceDatum N hN A hA S hS).chern) ≫
      projective φ N hN hA hB S hS =
      unit φ S ≫ ordinaryFiniteP1ChernPushforward B N hB S
        (projectiveLineTraceDatum N hN B hB S hS).chern) := by sorry

end AlgebraicGeometry.Etale.VectorTraceScalar
