/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib

/-!
# Étale covers of a normal scheme with separably closed function field

Let `S` be an integral normal scheme whose function field is separably closed, and let
`p : V ⟶ S` be separated and étale. Then `V` is a disjoint union of open subschemes of `S`.
This is rendered here as: there is an index type `ι` and a family of opens `U : ι → V.Opens`
which are pairwise disjoint, cover `V`, and are such that each composite `(U i).ι ≫ p` is an
open immersion.

Normality of `S` is not a notion available in Mathlib at the level of schemes, so it is taken
as the explicit hypothesis that every stalk of `S` is integrally closed; together with
`[IsIntegral S]` this says exactly that `S` is an integral normal scheme.

If moreover `V` is quasi-compact then the index type may be taken finite; this refinement is
`AlgebraicGeometry.Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField`.

The statements are the content of the blueprint subsection `sk-prop-etale-normal`; the proofs
are not given here.

## Main statements

- `AlgebraicGeometry.Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField`: a
  separated étale scheme over an integral normal base with separably closed function field is
  a disjoint union of opens of the base.
- `AlgebraicGeometry.Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField`:
  the same statement with finitely many pieces when the source is quasi-compact.

## References

- Stacks Project, Tag `09Z9`, <https://stacks.math.columbia.edu/tag/09Z9>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `sk-prop-etale-normal`: Étale covers of a normal scheme with separably closed
function field

Let `S` be an integral normal scheme — normality being spelled out as the hypothesis `hS`
that every stalk of `S` is integrally closed — whose function field `S.functionField` is
separably closed, and let `p : V ⟶ S` be separated and étale. Then `V` is the disjoint union
of a family of opens `U i` each of which maps isomorphically onto an open of `S`. -/
@[stacks 09Z9]
theorem Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField
    {V S : Scheme.{u}} [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] (p : V ⟶ S) [IsSeparated p] [Etale p] :
    ∃ (ι : Type u) (U : ι → V.Opens), (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧ ∀ i, IsOpenImmersion ((U i).ι ≫ p) :=
  sorry

/-- Blueprint `sk-prop-etale-normal`: Étale covers of a normal scheme with separably closed
function field

The quasi-compact refinement of
`AlgebraicGeometry.Etale.exists_opens_isOpenImmersion_of_isSepClosed_functionField`: if `V` is
in addition quasi-compact, then finitely many opens suffice. -/
@[stacks 09Z9]
theorem Etale.exists_finite_opens_isOpenImmersion_of_isSepClosed_functionField
    {V S : Scheme.{u}} [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    [IsSepClosed S.functionField] (p : V ⟶ S) [IsSeparated p] [Etale p] [CompactSpace V] :
    ∃ (ι : Type u) (_ : Finite ι) (U : ι → V.Opens), (∀ i j, i ≠ j → Disjoint (U i) (U j)) ∧
      (⨆ i, U i) = ⊤ ∧ ∀ i, IsOpenImmersion ((U i).ι ≫ p) :=
  sorry

end AlgebraicGeometry
