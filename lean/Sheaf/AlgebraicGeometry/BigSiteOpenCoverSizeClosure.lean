/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q32
-/
module

public import Sheaf.AlgebraicGeometry.StacksBigSiteCategory
public import Mathlib.AlgebraicGeometry.Restrict
import Sheaf.AlgebraicGeometry.SchemeSizeOpenCoverBound

/-! # Big sites contain schemes with bounded open covers

Source: Stacks Project, sets.tex, Tag 000R, lemma-what-is-in-it (6), using Tag 000Q,
lemma-bound-size, and Tag 000J, lemma-construct-category (2); topologies.tex,
Tag 021R, definition-big-fppf-site (2)
(blueprint: lem-sfb-big-site-open-cover-size-closure).

Only the chosen underlying full category matters for this assertion. Its admissibility
is the already defined `IsStacksBigSiteCategory`; no choice of covering families or
Grothendieck topology enters the size estimate. The explicit coding universe implements
the standing size convention, and cardinal lifts allow an arbitrary cover index universe.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A scheme with an open cover whose index cardinal and member sizes are bounded by
`s(T)^ℵ₀`, for an object `T` of the chosen big-site category, has a representative in
that same full category. The opens have their induced open subscheme structures.
The index set can be empty; there are no compactness or separation hypotheses.

Source: Stacks Project, sets.tex, Tag 000R, lemma-what-is-in-it (6), with Tag 000Q,
lemma-bound-size, and Tag 000J, lemma-construct-category (2); topologies.tex,
Tag 021R, definition-big-fppf-site (2)
(blueprint: lem-sfb-big-site-open-cover-size-closure).

Proof plan:
1. Apply `cardinalSize_le_openCover` [lem-sfb-scheme-size-open-cover-bound]. It bounds
   the size of X by max(ℵ₀, |I|, supᵢ s(Uᵢ)), including the empty cover.
2. Set κ = s(T) and K = κ^ℵ₀. The definition of cardinalSize gives ℵ₀ ≤ κ, and
   constant sequences give κ ≤ K. The two hypotheses bound |I| and every s(Uᵢ)
   by K, so their supremum and the whole maximum are at most K. Consequently
   s(X) ≤ K ≤ max(K, succ κ). Cardinal lifts only compare these in a common universe.
3. Apply [lem-sfb-big-site-bounded-size-representative] to this fixed chosen category,
   T and X. This is clause (2) of its admissibility predicate, and supplies an object
   X₀ and an isomorphism with X (reversing the isomorphism if necessary). For an empty
   index set the cover forces X to be empty; s(X) = ℵ₀ satisfies the same bound. -/
theorem exists_iso_of_openCover_cardinalSize_le
    (code : Scheme.{u} ↪ ZFSet.{u + 1}) (S₀ : Set Scheme.{u})
    (α : Ordinal.{u + 1}) (hα : IsStacksBigSiteCategory code S₀ α)
    (T : StacksBigSiteCategory code α) (X : Scheme.{u})
    {I : Type v} (U : I → X.Opens) (hU : (⨆ i : I, U i) = ⊤)
    (hI : Cardinal.lift.{u} (Cardinal.mk I) ≤
      Cardinal.lift.{v} (T.obj.cardinalSize ^ Cardinal.aleph0))
    (hsize : ∀ i : I, Cardinal.lift.{v} (U i).toScheme.cardinalSize ≤
      Cardinal.lift.{v} (T.obj.cardinalSize ^ Cardinal.aleph0)) :
    ∃ X₀ : StacksBigSiteCategory code α, Nonempty (X₀.obj ≅ X) := by
  sorry

end AlgebraicGeometry.Scheme
