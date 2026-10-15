/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.Zero
public import Sheaf.CategoryTheory.SiteCoveringAxioms

/-!
# Classes of indexed covering families

Source: Stacks Project, Sets, Section 000W, and Sites, Definition 00VH
(blueprint: def-weil-pbc-indexed-covering-class).
-/

@[expose] public section

universe u v w

namespace CategoryTheory.PreZeroHypercover

/-- The three covering axioms for a class of actual indexed families, without a smallness
or reindexing axiom. Source: Stacks Project, Sets, Section 000W; Sites, Definition 00VH
and its clarification that some choice of covering fibre products suffices
(blueprint: def-weil-pbc-indexed-covering-class).

The index universe `max u v w` may exceed both the object and arrow universes.
The ambient family type is one universe above this common universe. A set of families
is expressed by `Small.{max u v w}` of its subtype, rather than by an arbitrary predicate
on this large type. Families retain their index types and repeated arrows. -/
def IsCoveringClass {C : Type u} [Category.{v} C]
    (Cov : Set (Σ X : C, PreZeroHypercover.{max u v w} X)) : Prop :=
  (∀ (X Y : C) (f : Y ⟶ X), IsIso f → ⟨X, singleton f⟩ ∈ Cov) ∧
  (∀ (X : C) (E : PreZeroHypercover.{max u v w} X)
    (F : ∀ i : E.I₀, PreZeroHypercover.{max u v w} (E.X i)),
    ⟨X, E⟩ ∈ Cov → (∀ i, ⟨E.X i, F i⟩ ∈ Cov) → ⟨X, E.bind F⟩ ∈ Cov) ∧
  (∀ (X : C) (E : PreZeroHypercover.{max u v w} X), ⟨X, E⟩ ∈ Cov →
    ∀ (Y : C) (f : Y ⟶ X),
      ∃ (P : E.I₀ → C) (p : ∀ i, P i ⟶ Y) (q : ∀ i, P i ⟶ E.X i),
        (∀ i, IsPullback (p i) (q i) f (E.f i)) ∧
          ⟨Y, { I₀ := E.I₀, X := P, f := p }⟩ ∈ Cov)

end CategoryTheory.PreZeroHypercover
