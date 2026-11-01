/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarData

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open WeilConjectures.PurityFiniteSetting
namespace AlgebraicGeometry.Etale.VectorTraceScalar

variable {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]

/-- The ordered affine scalar square at one specified frame dimension.
Source: blueprint/latest, sec-smooth-purity/sk-prop-an, paragraph 2, affine counit
normalization.  This isolates the dimension-`r` affine component from the remaining
proper/open compact-support exchange.  Proof: the ordered affine scalar square over every
Noetherian `T` with `N` invertible and every dimension `d` is the hypothesis `ha` of the
frame comparison (the assumption of lem-pur-vector-scalar-frame-comparison); the statement
is its instance at `T` and `d`.
(blueprint: new-lem-pur-vector-scalar-frame-affine-component).
-/
theorem frame_scalar_restriction_affine (N : ℕ) (hN : 0 < N) (φ : A →+* B)
    (hA : (N : A) = 0) (hB : (N : B) = 0)
    (ha : ∀ (T : Scheme.{u}) [IsNoetherian T]
      (hT : IsUnit (N : Γ(T, ⊤))) (d : ℕ),
      affine φ N hN hA hB T hT d ≫ affineTrace N hN B hB T hT d =
        (scalarExtension φ T).map (affineTrace N hN A hA T hT d) ≫ unit φ T)
    (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤)))
    (d : ℕ) :
    affine φ N hN hA hB T hT d ≫ affineTrace N hN B hB T hT d =
      (scalarExtension φ T).map (affineTrace N hN A hA T hT d) ≫ unit φ T :=
  ha T hT d

end AlgebraicGeometry.Etale.VectorTraceScalar
