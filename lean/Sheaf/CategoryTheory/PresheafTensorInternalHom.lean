/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Objectwise tensor product and internal hom of presheaves

Source: the Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-presheaf.md`, clauses 1--2 and
both Hom formulas (blueprint: det-def-sfb-sheaf-tensor-presheaf).

The tensor is Mathlib's `Monoidal.functorCategoryMonoidal`; its symmetry is
`Monoidal.functorCategorySymmetric`. The internal hom is the existing
`Enriched.FunctorCategory.functorEnrichedHom`, not a second construction.
The only missing interface is existence of its ends for a possibly large essentially
small site. The theorem below supplies the global and slice end instances. With these,
`MonoidalClosed.FunctorCategory.monoidalClosed`,
`Presheaf.functorEnrichedHomCoyonedaObjEquiv`, and
`MonoidalClosed.FunctorCategory.homEquiv` give the remaining clauses of the node.
-/

@[expose] public section

universe uC vC uA vA w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory

/-- Existence of the global and slice ends used by the canonical presheaf internal hom.
The first family supplies the enriched bifunctor used by the closed structure, and the
second supplies the end at every object of the site. Neither the object universe of the
site nor either coefficient universe is identified with the smallness universe `w`.

Source: the Weil conjectures blueprint, `sec-proetale-coefficients`,
`sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-presheaf.md`, clause 2 and both
Hom formulas (blueprint: det-def-sfb-sheaf-tensor-presheaf).

Proof of the node, following its seven steps:
1. Use the pointwise tensor on functors: objects and arrows are tensor products of their
components, the unit is constant, and associators, unitors and symmetry are componentwise.
The coefficient coherence identities prove the presheaf identities after evaluation.
2. Choose a small full subcategory meeting every isomorphism class of the site. For a
fixed `U`, its arrows into `U` form a small full subcategory of `C/U` meeting every
isomorphism class, since the Hom sets are `w`-small. The same applies to `C` itself.
3. For either indexing category, take the equalizer of the two product maps between the
diagonal internal Homs and the mixed internal Homs indexed by arrows. The required small
products and equalizer exist by `lem-coef-grothendieck-small-limits`. Their universal
property identifies maps into this object with wedges. Extend a wedge from the small full
subcategory along chosen isomorphisms. The wedge equation makes this independent of the
isomorphism chosen and enforces the equation on every arrow. Thus it is an end over the
whole category, even when that category has a larger object universe. This proves the two
end-existence families stated below, without choosing an undetermined object.
4. For `u : U' ⟶ U`, reindex the wedge by composition `C/U' ⥤ C/U`. Uniqueness of maps to
the end proves the restriction identity and composition laws. Pre- and postcomposition
supply the contravariance in `F` and covariance in `G`.
5. Curry each wedge projection using the coefficient tensor--Hom adjunction. The wedge
equation becomes naturality of the maps `F(V) ⊗ B ⟶ G(V)` on the slice. Uncurrying is
inverse, giving `Presheaf.functorEnrichedHomCoyonedaObjEquiv` and compatibility with
restriction in `U`.
6. A transformation `χ : F ⊗ H ⟶ G` gives the local family at `U` whose component at
`v : V ⟶ U` is `F(V) ◁ H(v)` followed by `χ.app V`. Naturality of `χ` gives the wedge
equation, and uniqueness of maps to the end makes these families natural in `U`.
7. Conversely evaluate the family of `ψ : H ⟶ [F,G]` at the identity arrow of each slice.
Naturality of `ψ` recovers its other components; the wedge condition gives naturality of
`χ`. The constructions are inverse, and pre- and postcomposition commute with them.
This is `MonoidalClosed.FunctorCategory.homEquiv`, natural in all three variables, and
`MonoidalClosed.FunctorCategory.adj` gives the stated closed structure.
-/
theorem presheaf_enrichedHoms_exist
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
    [MonoidalPreadditive A] :
    (∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasEnrichedHom A F G) ∧
      (∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasFunctorEnrichedHom A F G) := by
  sorry

end CategoryTheory
