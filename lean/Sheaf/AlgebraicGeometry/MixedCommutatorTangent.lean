/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.GroupScheme.GeneralLinear.Lie

/-!
# Mixed commutators of infinitesimal matrix points

Source: Milne, Algebraic Groups (2017), Chapter 10, differential of multiplication and
commutator (blueprint: lem-wf-mixed-commutator-tangent).

An arbitrary finite basis identifies GL(V) with the general linear group scheme. The ring
`DualNumber (DualNumber k)` is k[ε,δ]/(ε²,δ²), with coordinates 1, ε, δ, εδ.
-/

@[expose] public section

universe u v

open CategoryTheory TrivSqZeroExt
open scoped MonObj Matrix

namespace AlgebraicGeometry.GeneralLinearGroup

/-- Over a field, two infinitesimal points of a closed subgroup of GL(V) base change to
k[ε,δ]/(ε²,δ²); their commutator is 1 + εδ(XY - YX), and the corresponding dual-number point
belongs to the subgroup. The finite basis `b` is arbitrary, including the empty basis.

Source: Milne, Algebraic Groups (2017), Chapter 10, differential of multiplication and
commutator (blueprint: lem-wf-mixed-commutator-tangent).

Proof: base change the two points along the inner and outer dual-number inclusions. Their
commutator remains a subgroup point by def-sc-group-scheme-subgroup. The inverses of 1 + εX
and 1 + δY are 1 - εX and 1 - δY. Multiply the four factors using ε² = δ² = 0:
first obtain 1 + εX + δY + εδXY, then 1 + δY + εδ(XY - YX), then 1 + εδ(XY - YX).
Here def-sc-dual-numbers supplies the nilpotent scalars. Finally use the injective map
`DualNumber.mulRingHom`, η ↦ εδ. Each defining equation of the closed subgroup, evaluated at
1 + η(XY - YX), has coefficients c + ηd. Its image is c + εδd and vanishes by the commutator
calculation. Independence of 1 and εδ forces c = d = 0. Thus the dual-number matrix satisfies
the defining equations and is invertible, with inverse 1 - η(XY - YX). -/
theorem mixedCommutator_tangent
    {k n : Type u} {V : Type v} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Fintype n] [DecidableEq n] (b : Module.Basis n k V)
    (G : Over (Spec (.of k))) [GrpObj G]
    (i : G ⟶ AlgebraicGeometry.GeneralLinearGroup n k) [IsClosedSubgroupScheme i]
    (X Y : Module.End k V) (x y : AlgebraicGeometry.points G (DualNumber k))
    (hx : homMulEquiv n k (DualNumber k) (x ≫ i) = dualUnit (LinearMap.toMatrix b b X))
    (hy : homMulEquiv n k (DualNumber k) (y ≫ i) = dualUnit (LinearMap.toMatrix b b Y)) :
    ∃ p q : AlgebraicGeometry.points G (DualNumber (DualNumber k)),
      homMulEquiv n k (DualNumber (DualNumber k)) (p ≫ i) =
        Matrix.GeneralLinearGroup.map (inlHom (DualNumber k) (DualNumber k))
          (dualUnit (LinearMap.toMatrix b b X)) ∧
      homMulEquiv n k (DualNumber (DualNumber k)) (q ≫ i) =
        Matrix.GeneralLinearGroup.map
          (DualNumber.mapRingHom (inlHom k k)) (dualUnit (LinearMap.toMatrix b b Y)) ∧
      (homMulEquiv n k (DualNumber (DualNumber k)) ((p * q * p⁻¹ * q⁻¹) ≫ i) :
        Matrix n n (DualNumber (DualNumber k))) =
        (1 + (LinearMap.toMatrix b b X).map (fun a ↦ inl (inr a))) *
        (1 + (LinearMap.toMatrix b b Y).map (fun a ↦ inr (inl a))) *
        (1 - (LinearMap.toMatrix b b X).map (fun a ↦ inl (inr a))) *
        (1 - (LinearMap.toMatrix b b Y).map (fun a ↦ inr (inl a))) ∧
      (homMulEquiv n k (DualNumber (DualNumber k)) ((p * q * p⁻¹ * q⁻¹) ≫ i) :
        Matrix n n (DualNumber (DualNumber k))) =
        1 + (LinearMap.toMatrix b b (X * Y - Y * X)).map (fun a ↦ inr (inr a)) ∧
      Function.Injective (DualNumber.mulRingHom (R := k)) ∧
      ∃ z : AlgebraicGeometry.points G (DualNumber k),
        homMulEquiv n k (DualNumber k) (z ≫ i) =
          dualUnit (LinearMap.toMatrix b b (X * Y - Y * X)) := by
  sorry

end AlgebraicGeometry.GeneralLinearGroup
