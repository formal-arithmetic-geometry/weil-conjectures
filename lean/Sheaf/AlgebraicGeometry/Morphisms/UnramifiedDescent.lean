/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Fpqc descent of unramified morphisms

Source: Stacks Project, Descent, Lemma 02VM, first assertion
(blueprint: lem-galois-fpqc-descend-unramified).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-galois-fpqc-descend-unramified) Stacks Project, Descent, Lemma 02VM,
first assertion. An unramified morphism descends along an fpqc covering of its target.
First descend local finite type by 02KX. The diagonal of each base change identifies with
the base change of the original diagonal, using the canonical pullback isomorphism and
cartesian-square pasting. Each resulting diagonal is an open immersion. Base change the
covering to the target of the original diagonal, then descend its open immersion by 02L3.
Local finite type and an open diagonal together give unramifiedness by Morphisms 02GE. -/
theorem locallyOfFiniteType_and_openDiagonal_of_fpqcCover
    {S X : Scheme.{u}} {I : Type v} {S' : I → Scheme.{u}}
    (f : X ⟶ S) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, LocallyOfFiniteType (pullback.snd f (g i)) ∧
      IsOpenImmersion (pullback.diagonal (pullback.snd f (g i)))) :
    LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f) := by
  sorry

end AlgebraicGeometry
