/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Standing.StandingExceptionalComposition

/-! # Explicit inverse candidate for the standing exceptional compositor

The inverse compact-support compositor is transposed in the reverse direction.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] standingExceptionalHomEquiv originCompositionAmbient
  rightDerivedLowerShriek rightDerivedUpperShriek

-- Keep the origin certificates as parameters so the public definitions use their own witnesses.
/- The compiled source definitions carry separate certificates for sheafification and
Grothendieck abelianness. Direct conversion of the resulting derived-category data is
expensive. Build explicit congruence proofs instead; the kernel checks the resulting term.
Adapted from the private transport in
WeilConjectures.SmoothPurity.Exceptional.ExceptionalSupportProjectionIso,
with heterogeneous function extensionality for the lambda motives in these definitions. -/
section StandingInstanceTransport
open Lean Meta Elab Tactic

end StandingInstanceTransport

set_option maxRecDepth 4096 in
set_option maxHeartbeats 400000 in
-- Allow the congruence tactic to traverse the two compiled instance-certificate expressions.
end AlgebraicGeometry.ProEtale
