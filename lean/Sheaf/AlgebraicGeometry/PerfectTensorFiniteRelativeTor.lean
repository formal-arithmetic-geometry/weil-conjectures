/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.FiniteTorDimensionOver
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Sheaf.AlgebraicGeometry.DerivedTensorStructure

/-! # Finite relative Tor dimension of a perfect tensor

Source: Stacks Project, Tags 0DJQ, 08CI and 08CG
(blueprint: lem-pc-perfect-tensor-finite-relative-tor).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- A perfect tensor with a bounded relatively flat complex has finite relative Tor
 dimension on a quasi-compact scheme. No coherence or proper support is needed.
Source: Stacks Project, Tag 0DJQ, proof of Lemma 36.27.2 (relative Tor verification),
and Tags 08CI and 08CG (bounded flat models and local Tor amplitude).

Proof:
1. By compactness take finitely many opens carrying strictly perfect representatives P_j
   of E. If [c,d] bounds G and [a_j,b_j] bounds P_j, the local derived tensor is represented
   by P_j tensor G, bounded in [a_j+c,b_j+d], because P_j is termwise flat over O_X.
2. The affine-section definition of IsFlatOver implies stalkwise relative flatness:
   localize the base at f(x) and take the filtered colimit of sections on affine
   neighbourhoods of x; localization and filtered colimits preserve flatness.
   After restriction of scalars to the inverse-image structure sheaf, every term of the
   total complex is a summand of a finite direct sum of terms of G. The assumed relative
   flatness of G therefore makes every term flat over the inverse-image structure sheaf.
3. Choose a single interval [a,b], with a <= b, containing all the finitely many local
   intervals (use [0,0] for an empty cover). By 08CI each local model has Tor amplitude
   in [a,b]. The definition of amplitude in 08CG is cohomology vanishing after derived
   tensor with any module sheaf; vanishing is local, so the bound holds globally.
4. Represent the global derived object by a complex K, and choose a K-flat resolution
   of its restriction of scalars. It computes the same relative derived tensors. The
   uniform bound from step 3 provides the witnesses in HasFiniteTorDimensionOver.
   Only a proposition of existence is asserted; no arbitrary witness defines new data.
(blueprint: lem-pc-perfect-tensor-finite-relative-tor). -/
theorem perfect_tensor_hasFiniteTorDimensionOver
    {X S : Scheme.{u}} [CompactSpace X] (f : X ⟶ S)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : IsPerfect X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hGflat : ∀ n : ℤ, Modules.IsFlatOver (G.X n) f) :
    HasFiniteTorDimensionOver f (E ⊗ DerivedCategory.Q.obj G) := by sorry

end AlgebraicGeometry.Scheme
