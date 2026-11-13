/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.Affine.Space.AffineSpaceIsoTraceCore

/-! # The affine-space trace under an arbitrary automorphism over its base -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- An arbitrary automorphism of the coordinate affine space preserves its ordered trace. -/
theorem affineSpaceIsoTraceInvariance (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ)
    (e : affineTraceTower S d ≅ affineTraceTower S d)
    (sq : IsPullback e.hom (affineTraceProjection S d)
      (affineTraceProjection S d) (𝟙 S)) :
    affineLinearTraceAction N hN A hA t S hS d e.hom sq ≫
        affineTraceCounit A N hA t D S hS d =
      affineTraceCounit A N hA t D S hS d := by
  rw [affineSpaceIsoTraceAction_eq_id N hN A hA t S hS d e sq]
  simp only [Category.id_comp]

end AlgebraicGeometry.Etale
