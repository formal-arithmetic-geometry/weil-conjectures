/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.PullbackStalkTensorComparison

/-! # Tor-independent perfect pullback comparison at a stalk

Source: Stacks Project, Tag 08IB, local affine Tor-independent tensor comparison
(blueprint: lem-pc-tor-independent-perfect-pullback-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u₁ w₁
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a Tor-independent square, the canonical base-derived tensor comparison
for a perfect object is an isomorphism at every pullback stalk in every degree.
The comparison is expressed in K-flat coordinates by `IsComparisonIso`, using
exactly the canonical map of `BaseDerivedTensorCohomologyModel`; invertibility
is invariant under the identification with the actual derived pullback stalk.

Source: Stacks Project, perfect.tex, Tag 08IB, local affine reduction
(blueprint: lem-pc-tor-independent-perfect-pullback-comparison).

Proof (the node's three steps):
1. Fix z and put R = O_{S,s}, A = O_{X,x}, B = O_{T,t}, C = O_{X',z}.
   On an affine neighbourhood of x, perfectness gives a bounded finite-projective
   model Q, by lem-pc-perfect-affine-bounded-projective.
2. The hypothesis gives Tor_i^R(A,B) = 0 for i > 0. Apply
   lem-pc-tor-independent-projective-complex-tensor to Q and the localization
   A tensor-over-R B -> C. Its map is the model's localizedComparison.
3. Restrict derived pullback to this neighbourhood by
   lem-pc-affine-derived-pullback-tensor-tilde. Its strictly perfect model is
   termwise flat, so lem-pc-flat-complex-derived-pullback computes its derived
   pullback termwise. Apply lem-weil-pbc-module-stalk-pullback degreewise to
   identify the target with Q tensor-over-A C. The ring map to C is a
   localization by the affine description of the fibre product; exactness of
   localization (lem-weil-pbc-localization-module-exact) commutes it with
   cohomology. These natural identifications identify the canonical map with
   Step 2. For any other K-flat representative, a common resolution and
   functoriality of derived tensor and pullback transport the same comparison.
   Postcomposition with any isomorphism of target coordinates preserves IsIso. -/
theorem torIndependent_perfect_pullback_comparison
    {X S T : Scheme.{u₁}} (f : X ⟶ S) (g : T ⟶ S)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w₁} (SheafOfModules.{u₁} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings (Limits.pullback f g).toRingedSpace))]
    (hTor : PullbackStalkTensor.IsTorIndependent f g)
    (P : schemeDerivedCategory X) (hP : Scheme.IsPerfect X P) :
    ∀ z : ↥(Limits.pullback f g), PullbackStalkTensor.IsComparisonIso f g P z := by
  sorry

end AlgebraicGeometry
