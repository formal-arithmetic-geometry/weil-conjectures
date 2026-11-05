/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.CategoryTheory.Preadditive.Basic

/-! # Scalar laws expressed using a named isomorphism -/

@[expose] public section

namespace CategoryTheory

/-- Replace a trivialization by an equal named isomorphism before taking components. -/
lemma purity_scalarDatum_iso_alias
    {C₀ C : Type*} [Category C₀] [Category C] [Preadditive C]
    (P : C₀ ⥤ C) (Q : C ⥤ C) (b : P ⋙ Q ≅ P)
    {M N : C₀} (e v : P.obj M ≅ P.obj N) (hv : v = e) (c : ℤ)
    (he : c • (b.hom.app M ≫ e.hom) = Q.map e.hom ≫ b.hom.app N) :
    c • (b.hom.app M ≫ v.hom) = Q.map v.hom ≫ b.hom.app N := by
  subst v
  exact he

/-- Transport a predicate `R x e` along an equality `x' = x` of indices and a heterogeneous
equality of values `v ≍ e`.

For a concrete instance, take for `R` a motive spelled exactly like the goal and obtain `x`
and `e` by unification from `he`. The kernel then never compares `x'` with `x` underneath a
projection such as `NatTrans.app`. It unfolds such projections before comparing their
arguments, so that comparison unfolds the whole concrete natural transformation. -/
lemma purity_motive_of_heq {α : Sort*} {β : α → Sort*} (R : ∀ x, β x → Prop) {x : α}
    {e : β x} (he : R x e) {x' : α} (h : x' = x) {v : β x'} (hv : v ≍ e) : R x' v := by
  subst h
  cases eq_of_heq hv
  exact he

end CategoryTheory
