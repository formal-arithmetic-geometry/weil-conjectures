/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Groupoid laws and the canonical stabilizer presheaf

Source: Stacks Project, spaces-groupoids.tex, definition-groupoid and
definition-stabilizer-groupoid (blueprint: def-sfb-algebraic-space-groupoid).

The laws are tested on every scheme over the base. Naturality is part of the maps.
The same definitions apply to presheaves, including the underlying presheaves of spaces.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Groupoid laws on all test-scheme points, with `c(a,b)` meaning `a` after `b`.
Source: Stacks, spaces-groupoids.tex, definition-groupoid and the following paragraph
(blueprint: def-sfb-algebraic-space-groupoid).
The source of the first arrow equals the target of the second in `Limits.pullback s t`.
The pullback universal property supplies every composable pair in the pointwise laws. -/
structure IsPresheafGroupoid {S : Scheme.{u}} {U R : (Over S)ᵒᵖ ⥤ Type u}
    (s t : R ⟶ U) (e : U ⟶ R) (i : R ⟶ R) (c : Limits.pullback s t ⟶ R) : Prop where
  source_id : e ≫ s = 𝟙 U
  target_id : e ≫ t = 𝟙 U
  source_inv : i ≫ s = t
  target_inv : i ≫ t = s
  source_comp : c ≫ s = Limits.pullback.snd s t ≫ s
  target_comp : c ≫ t = Limits.pullback.fst s t ≫ t
  id_comp : ∀ (H : Over S) (a : yoneda.obj H ⟶ R)
    (p : yoneda.obj H ⟶ Limits.pullback s t),
    p ≫ Limits.pullback.fst s t = a ≫ t ≫ e →
    p ≫ Limits.pullback.snd s t = a → p ≫ c = a
  comp_id : ∀ (H : Over S) (a : yoneda.obj H ⟶ R)
    (p : yoneda.obj H ⟶ Limits.pullback s t),
    p ≫ Limits.pullback.fst s t = a →
    p ≫ Limits.pullback.snd s t = a ≫ s ≫ e → p ≫ c = a
  inv_comp : ∀ (H : Over S) (a : yoneda.obj H ⟶ R)
    (p : yoneda.obj H ⟶ Limits.pullback s t),
    p ≫ Limits.pullback.fst s t = a ≫ i →
    p ≫ Limits.pullback.snd s t = a → p ≫ c = a ≫ s ≫ e
  comp_inv : ∀ (H : Over S) (a : yoneda.obj H ⟶ R)
    (p : yoneda.obj H ⟶ Limits.pullback s t),
    p ≫ Limits.pullback.fst s t = a →
    p ≫ Limits.pullback.snd s t = a ≫ i → p ≫ c = a ≫ t ≫ e
  assoc : ∀ (H : Over S) (p q r z : yoneda.obj H ⟶ Limits.pullback s t),
    p ≫ Limits.pullback.snd s t = q ≫ Limits.pullback.fst s t →
    r ≫ Limits.pullback.fst s t = p ≫ c →
    r ≫ Limits.pullback.snd s t = q ≫ Limits.pullback.snd s t →
    z ≫ Limits.pullback.fst s t = p ≫ Limits.pullback.fst s t →
    z ≫ Limits.pullback.snd s t = q ≫ c → r ≫ c = z ≫ c

/-- The canonical stabilizer `U ×_(U × U) R`, as an actual presheaf pullback.
The two maps into the product are the diagonal and `(s,t)`.
Source: Stacks, spaces-groupoids.tex, definition-stabilizer-groupoid; the order `(s,t)`
has the same inverse image of the diagonal as `(t,s)`
(blueprint: def-sfb-algebraic-space-groupoid). -/
def groupoidStabilizer {S : Scheme.{u}} {U R : (Over S)ᵒᵖ ⥤ Type u}
    (s t : R ⟶ U) : (Over S)ᵒᵖ ⥤ Type u :=
  Limits.pullback (prod.lift (𝟙 U) (𝟙 U)) (prod.lift s t)

end AlgebraicGeometry.AlgebraicSpace
