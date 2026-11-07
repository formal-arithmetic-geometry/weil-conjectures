/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
import Submission.WeilConjectures.AlgebraicGeometry.Local.LocalFibreDimensionOpen
import Submission.WeilConjectures.Topology.DimensionSupremumLocalDimensions

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Upper semicontinuity of proper fibre dimension

Source: Stacks Project, More on Morphisms, Tag 0D4I, lemma-dimension-fibres-proper
(blueprint: lem-weil-pbc-proper-fibre-dimension-upper-semicontinuous).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a proper morphism, the locus of fibres of dimension at most `d` is open.
The dimension of an empty fibre is bottom, so empty fibres belong to this locus.

Source: Stacks Project, More on Morphisms, Tag 0D4I, lemma-dimension-fibres-proper
(blueprint: lem-weil-pbc-proper-fibre-dimension-upper-semicontinuous).

Proof:
1. Properness gives local finite type (`def-weil-proper-morphism`,
   `def-weil-finite-type-morphism`). By `lem-weil-pbc-local-fibre-dimension-open`,
   the locus in `X` where the local dimension in the fibre is at most `d` is open.
   Its complement `Z`, where the local fibre dimension is greater than `d`, is closed.
2. Properness implies universal closedness (`def-weil-proper-morphism`), hence the
   image `f(Z)` is closed by applying universal closedness to the identity base change.
3. The fibre projection identifies its points with the inverse image of `s`
   (`def-pc-scheme-fibre`). The dimension of a fibre is the supremum of its local
   dimensions (`lem-weil-pbc-dimension-supremum-local-dimensions`). Thus `s` lies
   in `f(Z)` exactly when its fibre has dimension greater than `d`. For an empty
   fibre, the supremum is bottom and there is no point of `Z` over `s`.
4. The desired locus is the complement of the closed set `f(Z)`, hence is open.
   No Noetherian or flatness assumption enters the argument.
-/
theorem isOpen_setOf_topologicalKrullDim_fiber_le
    {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f] (d : ℕ) :
    IsOpen {s : S | topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞)} := by
  classical
  let U : Set X := {x | topologicalKrullDimAt (f.asFiber x) ≤ (d : WithBot ℕ∞)}
  have hU : IsOpen U := isOpen_localFibreDimension_le f d
  have hclosed : IsClosed (f '' Uᶜ) := f.isClosedMap _ hU.isClosed_compl
  have hpoint (s : S) (x : X) (hx : f x = s) :
      topologicalKrullDimAt (f.asFiber x) =
        topologicalKrullDimAt ((f.fiberHomeo s).symm ⟨x, hx⟩) := by
    subst s
    rfl
  have heq : {s : S | topologicalKrullDim (f.fiber s) ≤ (d : WithBot ℕ∞)} =
      (f '' Uᶜ)ᶜ := by
    ext s
    rw [Set.mem_ofPred_eq, topologicalKrullDim_eq_iSup_topologicalKrullDimAt, iSup_le_iff]
    constructor
    · intro hs ⟨x, hx, hxs⟩
      apply hx
      change topologicalKrullDimAt (f.asFiber x) ≤ (d : WithBot ℕ∞)
      rw [hpoint s x hxs]
      exact hs _
    · intro hs z
      let x : X := f.fiberι s z
      have hx : f x = s := by
        have hm : x ∈ f ⁻¹' {s} := by
          rw [← f.range_fiberι s]
          exact ⟨z, rfl⟩
        exact hm
      have hxU : x ∈ U := by
        by_contra hn
        exact hs ⟨x, hn, hx⟩
      change topologicalKrullDimAt (f.asFiber x) ≤ (d : WithBot ℕ∞) at hxU
      rw [hpoint s x hx] at hxU
      have hz : (f.fiberHomeo s).symm ⟨x, hx⟩ = z := by
        apply (f.fiberHomeo s).injective
        simp only [Homeomorph.apply_symm_apply]
        apply Subtype.ext
        rfl
      rwa [hz] at hxU
  rw [heq]
  exact hclosed.isOpen_compl

end AlgebraicGeometry
