/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Mathlib.Algebra.Homology.Homotopy
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic

/-! # Split top differential and canonical truncation

Source: Stacks Project, Tags 068V and 00MT, explicit split cancellation.
(blueprint: lem-pc-split-top-differential-cancellation-homotopy)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

/-- Canonical truncation at a split top differential preserves homotopy type.

Source: Stacks Project, Tags 068V and 00MT, split identity-pair cancellation.
(blueprint: lem-pc-split-top-differential-cancellation-homotopy).

Proof: Write δ for the differential from m to m+1 and σ for a section of δ.
The canonical truncation has cycles (the kernel of δ) in degree m, the original
terms below m, and zero above m. The map id - δ ≫ σ factors uniquely through
cycles. Together with identities below m and zero maps above m, this defines a
chain map r from B to its truncation. The consecutive-differential equation
proves the chain-map identity entering degree m; the kernel equation proves the
one leaving it. The canonical inclusion i satisfies i ≫ r = id. The family
with σ in degree m+1 to m and zero elsewhere is a homotopy between r ≫ i and id:
in degree m its boundary is δ ≫ σ, in degree m+1 it is σ ≫ δ = id, and in all
other degrees it vanishes. Terms above m+1 are zero by the support assumption.
Transport these equations through the canonical term isomorphisms of truncLE
and assemble HomotopyEquiv. This works also for m=0 and for zero terms. -/
theorem split_top_differential_cancellation_homotopy
    (S : Scheme.{u}) (B : CochainComplex S.Modules ℤ) (m : ℕ)
    (hBle : B.IsStrictlyLE (m + 1 : ℕ))
    (hsplit : IsSplitEpi (B.d (m : ℤ) (m + 1 : ℕ))) :
    Nonempty (HomotopyEquiv (B.truncLE m) B) := by sorry

end AlgebraicGeometry.Scheme.Modules
