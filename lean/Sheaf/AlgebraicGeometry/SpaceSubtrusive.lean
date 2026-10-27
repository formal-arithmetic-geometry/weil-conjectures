/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.AlgebraicGeometry.SpaceConstructibleTopology
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers

/-! # Subtrusive and universally submersive morphisms

Source: Rydh, Remark (1.8), Definition (2.2), and the paragraph before Proposition (2.4),
pp.6--8 (blueprint: def-sfb-space-subtrusive-morphisms).

The affine-test predicate is defined on presheaf maps so it can be applied directly to
the canonical sheaf fibre-product projection, without choosing another pullback object.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- Subtrusiveness: constructible quotient (including surjectivity) and lifting every
Zariski specialization pair. The orientation is `y₁ ⤳ y₀`, so `y₀ ∈ closure {y₁}`.
Source: Rydh, Proposition (2.1)(i) and Definition (2.2), p.7
(blueprint: def-sfb-space-subtrusive-morphisms). -/
def MapIsSubtrusive {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) : Prop :=
  @Topology.IsQuotientMap (Point F) (Point G)
    (pointConstructibleTopology F) (pointConstructibleTopology G) (mapPoint f) ∧
  ∀ (y₀ y₁ : Point G), y₁ ⤳ y₀ →
    ∃ (x₀ x₁ : Point F), x₁ ⤳ x₀ ∧ mapPoint f x₀ = y₀ ∧ mapPoint f x₁ = y₁

/-- Universal subtrusiveness, tested after every affine scheme base change.
Source: Rydh, Definition (2.2), Remark (1.8) and Proposition (2.4)(ii), pp.6--8
(blueprint: def-sfb-space-subtrusive-morphisms). -/
def MapIsUniversallySubtrusive {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) : Prop :=
  ∀ (T : Over S) (a : yoneda.obj T ⟶ G), IsAffine T.left →
    MapIsSubtrusive (Limits.pullback.snd f a)

/-- Universal submersiveness: every algebraic-space base change is a surjective quotient
map for the Zariski point topology. No quasi-compactness or representability is imposed.
Source: Rydh, definition of submersions and Remark (1.8), pp.5--6
(blueprint: def-sfb-space-subtrusive-morphisms). -/
def MapIsUniversallySubmersive {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) : Prop :=
  ∀ (Y' : AlgebraicSpace S) (g : Y'.obj.obj ⟶ G),
    Topology.IsQuotientMap (mapPoint (Limits.pullback.snd f g))

end AlgebraicGeometry.AlgebraicSpace
