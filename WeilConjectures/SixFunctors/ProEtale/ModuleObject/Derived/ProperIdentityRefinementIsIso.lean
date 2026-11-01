/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing

/-! # Invertibility of the proper identity refinement

This isolates the geometric input used by proper compactification coincidence.
(blueprint: sk-prop-sf-comp-proper).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

open CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Every refinement from the identity compactification of a proper morphism is
invertible in the native condensed derived category.

Source: the first proof step of `sk-prop-sf-comp-proper`, sentence “For any
other compactification its open is clopen”; the clopen restriction calculation
is the missing all-coefficient form of the rational refinement theorem.

Proof in words: the section of the pullback of the target open is simultaneously
open and closed.  The clopen decomposition gives the refinement map as the
identity on the selected component and zero on its complement.  Restriction to
the two complementary opens detects isomorphisms, so the refinement natural
transformation is an isomorphism on the whole derived category.  This argument
uses no coefficient finiteness hypothesis.
(blueprint: sk-prop-sf-comp-proper). -/
theorem properIdentityRefinement_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (c : Compactification f)
    (r : (Compactification.ofIsProper f).Refinement c) :
    IsIso (refinement Λ r) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
