/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import Sheaf.Topology.RingedSpaceModuleCohomology

/-! # A step in projective Serre vanishing -/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The descending Serre induction step, simultaneously for all coherent coefficients.
Source: Stacks Project, Tag 01YS (4), proof of part (4).
(blueprint: lem-pc-j4-closed-immersion-twist-vanishing-step)

Proof: Apply the hypothesis to the identity immersion of projective space. This gives
next-degree vanishing for every coherent ambient module, in particular the kernel of
a finite sum of twists surjecting onto i_*F. The kernel is coherent over the Noetherian
base. Tensor this exact sequence by the invertible O(t). For large t the finite sum
has zero positive-degree cohomology by the projective twist computation, and the
hypothesis kills the next-degree cohomology of the kernel. The long exact sequence
kills degree q of the twisted pushforward. The projection formula and the closed
immersion cohomology comparison transfer this vanishing to X. Take the maximum of
the two integer thresholds and zero to obtain a natural-number threshold. -/
theorem exists_isZero_closedImmersion_twist_of_next_degree
    (A : Type u) [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}} {N : ℕ}
    (i : X ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion i]
    (q : ℕ) (hq : 0 < q)
    (hnext : ∀ {Y : Scheme.{u}}
      (j : Y ⟶ ℙ(ULift.{u} (Fin (N + 1)); Spec (.of A))) [IsClosedImmersion j]
      (F : Y.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation],
      ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
        IsZero ((RingedSpace.moduleCohomology Y.toRingedSpace (q + 1)).obj
          (tensorObj F (ProjectiveSpace.twistRestrict j t))))
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFinitePresentation] :
    ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
      IsZero ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
        (tensorObj F (ProjectiveSpace.twistRestrict i t))) := by sorry

end AlgebraicGeometry.Scheme.Modules
