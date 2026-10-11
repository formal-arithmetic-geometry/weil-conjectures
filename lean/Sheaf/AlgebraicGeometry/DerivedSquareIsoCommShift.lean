/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Shift.CommShift
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs

/-!
# Shift compatibility of the derived square isomorphism

Source: literature/stacks-project/derived.tex, Definition 014V and Lemma 05SU
(blueprint: lem-weil-pbc-derived-square-iso-commshift).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The derived square comparison for a cartesian square is compatible with all shifts.
Source: literature/stacks-project/derived.tex, Definition 014V and Lemma 05SU
(blueprint: lem-weil-pbc-derived-square-iso-commshift).
The comparison uses only the commutativity of the cartesian square; its chosen
identification with the fiber product is recovered by `sq.isoPullback`.

Proof (the node's seven steps):
1. On unbounded derived categories, the factorization identifications
   `β_u : u⁻¹_D Q ≅ Q u⁻¹` commute with shifts by
   `lem-weil-pbc-exact-functor-derived-factorization`. Termwise pullback is additive,
   so it preserves the shifted differential `-d` and its termwise shift isomorphism
   is the identity. The localization functor `Q` carries its canonical shift structure.
2. Whisker and compose these identifications to obtain shift-compatible `β₁, β₂`
   for the two composite pullbacks, using
   `lem-weil-pbc-commshift-nattrans-comp-whisker`. Naturality of the outer shift
   isomorphism moves the inner factorization past it; apply the compatibility of
   each `β_u` in turn. This gives the composite shift isomorphisms `φ, ψ`.
3. The termwise square comparison at `K[1]` and the shift of its comparison at `K`
   have the same degree `r` component, namely the sheaf comparison at `K^(r+1)`.
   Naturality of the shift isomorphism of `Q` gives compatibility after localization.
4. At `QK`, write the derived comparison as `β₂⁻¹ ∘ Q(θ_K) ∘ β₁`.
   Precompose the desired identity with the isomorphism obtained
   by pulling back `Q(K[1]) ≅ (QK)[1]`. Naturality of the derived comparison,
   Step 2 for `β₂`, Step 3, and Step 2 for `β₁` identify the two composites.
   Cancel the precomposed isomorphism.
5. The two sides are natural transformations on the unbounded derived category.
   They agree after precomposition with `Q` by Step 4, hence agree everywhere by
   `lem-weil-pbc-localization-universal-property` (`Localization.natTrans_ext`).
6. Restrict this identity to the full bounded below subcategories. Pullbacks and
   their shift structures are the restrictions of the unbounded ones, by
   `def-weil-pbc-derived-inverse-image` and
   `lem-weil-pbc-triangulated-functor-restriction`; the square comparison restricts
   as in `def-weil-pbc-derived-square-iso`.
7. The zero shift is the identity. Induct on positive shifts by composing and
   shifting the identity for `[1]`; obtain negative shifts by applying the positive
   identity at `M[-m]`, inverting the shift isomorphisms, and shifting back.
   Thus `NatTrans.CommShift` holds for all integers with the canonical shift coherences.
-/
theorem derivedSquareIso_commShift
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) :
    NatTrans.CommShift
      (Etale.pullbackSquareComparison (AddCommGrpCat.{u + 1}) sq.toCommSq).hom ℤ := by
  sorry

end AlgebraicGeometry
