/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus

/-! # Pullback transport indexed by equality of morphisms -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

/-- Transport pullback by induction on the morphism equality, keeping the
transport indexed by morphisms rather than by equality of entire derived functors.
Source: Stacks 03CB and the equality transport in the ordinary proper/open calculus.
(blueprint: def-sf-morphism-pullback-congruence). -/
def morphismPullbackCongr
    {G : Type*} [Category G] {geo : G ⥤ Scheme.{u}} (c : Calculus G geo)
    {X Y : G} {f g : X ⟶ Y} (h : f = g) : c.P f ≅ c.P g :=
  h ▸ Iso.refl _

/-- The morphism-indexed transport is the specified equality transport.
Source: equality induction; Stacks 03CB.
(blueprint: def-sf-morphism-pullback-congruence).
Proof: after induction on the morphism equality, both sides are the identity. -/
theorem morphismPullbackCongr_eq
    {G : Type*} [Category G] {geo : G ⥤ Scheme.{u}} (c : Calculus G geo)
    {X Y : G} {f g : X ⟶ Y} (h : f = g) :
    morphismPullbackCongr c h = c.pCongr h := by
  cases h
  rfl

end AlgebraicGeometry.ProEtale.AmbientProperOpen
