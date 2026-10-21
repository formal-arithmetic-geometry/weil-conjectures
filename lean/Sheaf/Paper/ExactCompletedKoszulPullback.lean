/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.Paper.ConstantCompletionEquivalence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! # Koszul units under exact inverse image preserving products

Source: Stacks Project, algebraization.tex, Tag 0A0E; sites-cohomology.tex, Tags
07A4 and 0941 (blueprint: lem-sfb-exact-completed-koszul-pullback).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

/-- Exact inverse image preserving countable products transports the actual Koszul unit.

Source: Stacks Project, algebraization.tex, Tag 0A0E, proof by the augmented finite
Koszul tower; sites-cohomology.tex, Tags 07A4 and 0941.
(blueprint: lem-sfb-exact-completed-koszul-pullback).

Proof: the coefficient isomorphism identifies pure module inverse image with the
specified module pullback. This is additive and exact. Forgetting module structure
computes products, so the assumed product preservation on sheaves gives invertible
canonical product comparisons on modules. The canonical tensor comparison identifies
pullback of each rank-one Koszul factor with the corresponding factor over the target
ring. Naturality of the constant-ring comparison identifies the scalar powers and the
transitions. Iterating tensor comparison gives an isomorphism of strict tensor towers,
natural in the complex, carrying the degree-zero augmentation to the target
augmentation. Since the module functor is exact, it inverts quasi-isomorphisms and its
left derived comparison is invertible on every complex. The strict Roos comparison
computes inverse limit by the shifted cone of one minus the shift. The product
comparison intertwines the shift by its projection formula and preserves both summands
of the cone. It carries the augmentation with coordinates (gamma, zero) to the target
augmentation with those same coordinates. Descend the tower isomorphism and this
normalized cone comparison through localization. Uniqueness of the derived tensor
tower and of derived inverse limit identifies the resulting functors with the supplied
presentations. Their prescribed units are defined by precisely these augmentations,
which proves the displayed unit equation. For no generators the sole factor is the
unit complex; zero scalars, units, and zero coefficient rings satisfy the same formulas.
-/
theorem exactCompletedKoszulPullback
    {C D : Type v} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
    (F : InverseImageData L) (V : Sheaf K (Type v) ⥤ Sheaf J (Type v))
    (adj : L ⊣ V) [PreservesFiniteLimits L]
    [PreservesLimitsOfShape (Discrete ℕ) L]
    (A : Type v) [CommRing A] (I : Ideal A)
    [IsIso (completedMap F A I)]
    [HasExactLimitsOfShape (Discrete ℕ) (Mod (completed J A I))]
    [HasExactLimitsOfShape (Discrete ℕ) (Mod (completed K A I))]
    (r : ℕ) (a : Fin r → A)
    (PX : KoszulPresentation J A I true r a)
    (PS : KoszulPresentation K A I true r a) :
    ∃ e : koszulCompletion J A I PX ⋙ (derivedPull F V adj (completedMap F A I)).functor ≅
        (derivedPull F V adj (completedMap F A I)).functor ⋙ koszulCompletion K A I PS,
      ∀ M, (derivedPull F V adj (completedMap F A I)).functor.map
          (koszulUnit J A I PX M) ≫ e.hom.app M =
        koszulUnit K A I PS ((derivedPull F V adj (completedMap F A I)).functor.obj M) := by
  sorry

end CategoryTheory.ConstantCompletion
