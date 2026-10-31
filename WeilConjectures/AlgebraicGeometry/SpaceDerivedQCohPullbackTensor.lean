/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceDerivedTensorPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorQCohSupplement
import WeilConjectures.AlgebraicGeometry.RingedTopoiCanonicalTensorPullbackOfUniverses

/-! # Derived pullback and tensor preserve quasi-coherence on algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tags 08F4 and 08F5
(blueprint: lem-sfb-space-derived-qcoh-pullback-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u wX wY wZ
open CategoryTheory
namespace AlgebraicGeometry.AlgebraicSpace

/-- Derived pullback and derived tensor preserve quasi-coherent cohomology, unboundedly.
Source: Stacks Project, Derived Categories of Spaces, Tags 08F4 and 08F5
(blueprint: lem-sfb-space-derived-qcoh-pullback-tensor).

Proof: the pullback clause of lem-sfb-space-derived-etale-chart-calculus, applied
with u = a, gives the first assertion. For tensor, first work on a scheme U on its
small etale site. The equivalence of lem-sfb-scheme-derived-etale-qcoh-comparison
writes both objects as exact epsilon-pullbacks of Zariski quasi-coherent objects.
The scheme tensor clause of lem-pc-derived-pullback-tensor-qcoh makes their tensor
quasi-coherent on the Zariski site. The exact epsilon-pullback equals its derived
functor, and lem-weil-pbc-ringed-topoi-derived-tensor-pullback identifies its image
with the tensor on U_et. For a general space choose a surjective etale scheme atlas.
The chart calculus identifies atlas pullback with exact restriction. The same
ringed-topos tensor comparison identifies restriction of the tensor with the tensor
of the restrictions. The scheme case makes it quasi-coherent, and the covering
criterion of lem-sfb-space-derived-etale-chart-calculus gives quasi-coherence on
Z. All these operations transport through the specified small ringed model
and apply to arbitrary unbounded complexes, without finiteness or separation. -/
theorem spaceDerivedPullback_tensor_preserve_QCoh
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [HasDerivedCategory.{wX} X.SmallModules] [HasDerivedCategory.{wY} Y.SmallModules]
    (a : X ⟶ Y) :
    (∀ K : Y.DerivedModules, Y.derivedQCohProperty K →
      X.derivedQCohProperty ((derivedTensorPullback a).obj K)) ∧
    (∀ (Z : AlgebraicSpace S) [HasDerivedCategory.{wZ} Z.SmallModules]
      (K L : Z.DerivedModules), Z.derivedQCohProperty K → Z.derivedQCohProperty L →
      Z.derivedQCohProperty (Z.derivedDualityModel.closed.tensor.obj (K, L))) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
