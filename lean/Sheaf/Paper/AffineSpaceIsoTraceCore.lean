/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.AffineLinearTraceAction

/-! # Identity of the arbitrary affine-space trace action -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- The geometric degree-one calculation for an arbitrary affine-space isomorphism makes
the induced compact-support action the identity.

Source: latest blueprint sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2; fixed-base presentation invariance,
proof step 1 (blueprint: affine-space trace invariance core).

Proof: compact-support base change and the canonical coefficient descent identify the
action on a geometric stalk with pullback on the top compact-support class of affine
d-space over a separably closed field. The ordered one-dimensional Kummer normalization
sends every rational point class to one; the open-closed sequence for the projective line
and induction over the coordinate tower show that these classes generate the top group.
An isomorphism carries a rational point to its unique inverse image with local
multiplicity one, so it fixes the normalized generator. Thus the action is the identity
on every geometric stalk. The degree-zero single functor is faithful and geometric
stalks are conservative, giving the derived equality. The cases d=0, an empty base,
and the zero coefficient ring use the identity and zero-object equations.
-/
theorem affineSpaceIsoTraceAction_eq_id (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (d : ℕ)
    (e : affineTraceTower S d ≅ affineTraceTower S d)
    (sq : IsPullback e.hom (affineTraceProjection S d)
      (affineTraceProjection S d) (𝟙 S)) :
    affineLinearTraceAction N hN A hA t S hS d e.hom sq = 𝟙 _ := by
  sorry

end AlgebraicGeometry.Etale

