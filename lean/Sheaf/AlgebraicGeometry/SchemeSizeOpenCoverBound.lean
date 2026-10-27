/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Sheaf.AlgebraicGeometry.SchemeCardinalSize
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Scheme size bounded by an open cover

Source: Stacks Project, sets.tex, Tag 000Q, lemma-bound-size, with the countable
cardinal included to cover the empty covering of the empty scheme
(blueprint: lem-sfb-scheme-size-open-cover-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgebraicGeometry.Scheme

/-- The cardinal size of a scheme is bounded by the number of members of an open cover
and their cardinal sizes, together with the countable cardinal. The opens carry their
induced scheme structures. The covering index may be empty, and no quasi-compactness
or quasi-separatedness is assumed. Cardinal lifts only place the scheme and index
cardinals in a common universe.

Source: Stacks Project, sets.tex, Tag 000Q, lemma-bound-size, with the explicit countable
cardinal correction for the empty covering
(blueprint: lem-sfb-scheme-size-open-cover-bound).

Proof plan: apply [lem-sfb-open-cover-scheme-size] with Y = X and Yᵢ = (U i).toScheme.
Its definition of size is exactly [def-sfb-scheme-cardinal-size], and its cover has the
same induced open subscheme structures, arbitrary index set, and no compactness or
separation hypotheses. Its conclusion is precisely the displayed maximum after lifting
cardinals to the common universe. It explicitly permits the empty covering, whose
supremum is zero, so the countable term also gives the empty-scheme case. -/
theorem cardinalSize_le_openCover (X : Scheme.{u}) {I : Type v} (U : I → X.Opens)
    (hU : (⨆ i : I, U i) = ⊤) :
    Cardinal.lift.{v} X.cardinalSize ≤
      max Cardinal.aleph0
        (max (Cardinal.lift.{u} (Cardinal.mk I))
          (⨆ i : I, Cardinal.lift.{v} (U i).toScheme.cardinalSize)) := by
  sorry

end AlgebraicGeometry.Scheme
