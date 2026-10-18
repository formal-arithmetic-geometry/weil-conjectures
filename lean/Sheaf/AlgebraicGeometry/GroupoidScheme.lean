/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q05
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Groupoid laws for schemes

Source: Stacks Project, Groupoids, Definition 0231 and the preceding groupoid axioms
(blueprint: def-a1-groupoid-scheme).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The supplied morphisms define a groupoid on points of every test scheme.
Source: Stacks Project, Tag 0231, including the preceding explicit groupoid axioms
(blueprint: def-a1-groupoid-scheme). This is the absolute version, equivalently over Spec Z.
Composition is ordered `c(a,b) = a ∘ b`, with `s(a) = t(b)`. The compatibility proofs
in the last five fields are universally quantified: the first six fields ensure their
existence, so none of those laws is vacuous. Naturality in the test scheme follows from
composition of scheme morphisms and the universal property of the pullback. -/
structure IsGroupoidScheme {U R : Scheme.{u}} (s t : R ⟶ U) (e : U ⟶ R)
    (i : R ⟶ R) (c : pullback s t ⟶ R) : Prop where
  identity_source : e ≫ s = 𝟙 U
  identity_target : e ≫ t = 𝟙 U
  inverse_source : i ≫ s = t
  inverse_target : i ≫ t = s
  composition_source : c ≫ s = pullback.snd s t ≫ s
  composition_target : c ≫ t = pullback.fst s t ≫ t
  identity_comp : ∀ (H : Scheme.{u}) (a : H ⟶ R)
    (h : (a ≫ t ≫ e) ≫ s = a ≫ t),
    pullback.lift (a ≫ t ≫ e) a h ≫ c = a
  comp_identity : ∀ (H : Scheme.{u}) (a : H ⟶ R)
    (h : a ≫ s = (a ≫ s ≫ e) ≫ t),
    pullback.lift a (a ≫ s ≫ e) h ≫ c = a
  inverse_comp : ∀ (H : Scheme.{u}) (a : H ⟶ R)
    (h : (a ≫ i) ≫ s = a ≫ t),
    pullback.lift (a ≫ i) a h ≫ c = a ≫ s ≫ e
  comp_inverse : ∀ (H : Scheme.{u}) (a : H ⟶ R)
    (h : a ≫ s = (a ≫ i) ≫ t),
    pullback.lift a (a ≫ i) h ≫ c = a ≫ t ≫ e
  associative : ∀ (H : Scheme.{u}) (a b d : H ⟶ R)
    (hab : a ≫ s = b ≫ t) (hbd : b ≫ s = d ≫ t)
    (hl : (pullback.lift a b hab ≫ c) ≫ s = d ≫ t)
    (hr : a ≫ s = (pullback.lift b d hbd ≫ c) ≫ t),
    pullback.lift (pullback.lift a b hab ≫ c) d hl ≫ c =
      pullback.lift a (pullback.lift b d hbd ≫ c) hr ≫ c

end AlgebraicGeometry
