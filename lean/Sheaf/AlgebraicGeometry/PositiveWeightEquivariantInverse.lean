/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.AlgebraicGeometry.AffinePointTangent
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Topology.Connected.Basic

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.AlgebraicGeometry.Spec

/-! # A global inverse from positive tangent weights

Source: Milne, Algebraic Groups (2017), Corollary 13.42 and its proof, p.270,
using Theorem 13.41, pp.269--270
(blueprint: lem-sfb-positive-weight-equivariant-inverse).

We write the arbitrary affine F-schemes as Spec A and Spec B. Their rational points
are algebra maps to F, and their tangent spaces are the duals of the corresponding
kernel ideals modulo their squares. No choice of coordinates or generators is imposed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- An equivariant map between smooth connected affine schemes is an isomorphism
when its differential at a fixed point is invertible and the source tangent weights
are strictly positive integers. `hdf` characterizes the differential on every function:
its point derivation is precomposition with pullback. Thus it is exactly the dual
of pullback on the cotangent quotients, rather than an arbitrary linear equivalence.
Source: Milne, Corollary 13.42, p.270
(blueprint: lem-sfb-positive-weight-equivariant-inverse).

Proof plan, following the three steps of the node:
1. Cotangent spaces are finite dimensional by
   lem-sfb-fixed-point-homogeneous-cotangent-lifts. Dualize the inverse differential
   and use double dual evaluation to see that the cotangent pullback is invertible.
   Differentiate the scheme equivariance identity; it intertwines the tangent
   actions, so the target has the same strictly positive character weights.
2. Choose homogeneous lifts b_i of a target cotangent basis using that same lemma.
   Their pullbacks a_i are a homogeneous source cotangent basis, with the same
   weights by equivariance. Apply lem-sfb-positive-weight-luna-coordinates to both
   families. Smoothness, connectedness, affineness and finite type hold on both
   sides. The resulting maps lambda_Y and lambda_X to affine d-space are isomorphisms.
3. By def-weil-pbc-mv-polynomial-ring the maps lambda_Y composed with f and lambda_X
   agree: each polynomial generator pulls back to a_i. The affine spectrum
   correspondence of def-weil-affine-spectrum identifies the scheme morphisms.
   Hence f = lambda_Y inverse composed with lambda_X and has the inverse
   lambda_X inverse composed with lambda_Y. If d = 0, use the empty polynomial
   ring F. Character weights, never differentials of characters, make the argument
   valid in every characteristic, including when a weight is divisible by it. -/
theorem isIso_of_positive_tangent_weights
    {F A B : Type u} [Field F] [IsAlgClosed F]
    [CommRing A] [Algebra F A] [CommRing B] [Algebra F B]
    [Smooth (StandardGroupSchemes.affine F A).hom]
    [Smooth (StandardGroupSchemes.affine F B).hom]
    [ConnectedSpace (StandardGroupSchemes.affine F A).left]
    [ConnectedSpace (StandardGroupSchemes.affine F B).left]
    [LocallyOfFiniteType (StandardGroupSchemes.affine F A).hom]
    [QuasiCompact (StandardGroupSchemes.affine F A).hom]
    [LocallyOfFiniteType (StandardGroupSchemes.affine F B).hom]
    [QuasiCompact (StandardGroupSchemes.affine F B).hom]
    [ModObj (StandardGroupSchemes.multiplicative F) (StandardGroupSchemes.affine F A)]
    [ModObj (StandardGroupSchemes.multiplicative F) (StandardGroupSchemes.affine F B)]
    (x : A →ₐ[F] F) (y : B →ₐ[F] F) (φ : B →ₐ[F] A)
    (hpoint : x.comp φ = y)
    (hxfixed : lift (𝟙 (StandardGroupSchemes.multiplicative F))
        (toUnit (StandardGroupSchemes.multiplicative F) ≫
          StandardGroupSchemes.identitySection F x) ≫
        ModObj.smul (M := StandardGroupSchemes.multiplicative F)
          (X := StandardGroupSchemes.affine F A) =
      toUnit (StandardGroupSchemes.multiplicative F) ≫
        StandardGroupSchemes.identitySection F x)
    (hyfixed : lift (𝟙 (StandardGroupSchemes.multiplicative F))
        (toUnit (StandardGroupSchemes.multiplicative F) ≫
          StandardGroupSchemes.identitySection F y) ≫
        ModObj.smul (M := StandardGroupSchemes.multiplicative F)
          (X := StandardGroupSchemes.affine F B) =
      toUnit (StandardGroupSchemes.multiplicative F) ≫
        StandardGroupSchemes.identitySection F y)
    [IsModHom (StandardGroupSchemes.multiplicative F) (StandardGroupSchemes.map F φ)]
    (hdf : ∃ e : ((RingHom.ker x).Cotangent →ₗ[F] F) ≃ₗ[F]
        ((RingHom.ker y).Cotangent →ₗ[F] F),
      ∀ (v : (RingHom.ker x).Cotangent →ₗ[F] F) (b : B),
        y.cotangentDerivation (e v) b = x.cotangentDerivation v (φ b))
    (hweights : AffinePointTangent.HasPositiveWeights x) :
    IsIso (StandardGroupSchemes.map F φ) := by
  sorry

end AlgebraicGeometry
