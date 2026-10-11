/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
import Sheaf.AlgebraicGeometry.TorsionAbelianBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Target locality of proper base change

Source: Stacks Project, Tags 0EZR, 0D6G and the first paragraph of Tag 0A4F
(blueprint: lemma-weil-pbc-target-locality).

## Main statements

* `AlgebraicGeometry.Etale.derivedBaseChange_target_locality`: cartesianness of the
  localized square, the individual restriction criterion, and detection on the cover.
* `AlgebraicGeometry.Etale.hasTorsionAbelianBaseChange_of_etale_cover`: properness of
  the base changes and descent of PBC from the target cover.

Fibre products are specified by their projections and universal properties. This allows
any chosen fibre product, including `Limits.pullback`, without choosing new definitions.
-/

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Target locality of the specified exchange morphism. Source: Stacks Project, Tags
0EZR, 0D6G, 0EZS and 0A4F (blueprint: lemma-weil-pbc-target-locality).

The three families of pullback squares are the base change of `f` along `j i`, of `g`
along `j i`, and of `f'` along `k i`. The map `g'i i` has the two prescribed components:
`hcomponent` gives its component to `X`, while `sqᵢ` gives its component to `V i`.

Proof:
1. Paste the square of `f'` and `k i` with `sq`. The resulting rectangle is cartesian.
   Cancel the cartesian square of `f` and `j i` to obtain the localized cartesian square
   (`lem-weil-pbc-cartesian-square-pasting`).
2. The `k i` form an etale cover, being the base change of the `j i`
   (`lem-weil-pbc-etale-covering-base-change`).
3. Factor the exchange map of the rectangle in two ways, first through restriction by
   `k i`, then through the localized exchange map, inserting inverse-image composition
   isomorphisms (`lem-weil-pbc-exchange-identity-pasting`).
4. The intervening exchange maps along `j i` and `k i` are isomorphisms by etale
   localization (`lem-weil-pbc-etale-localization-exchange`, Tag 0D6G). Cancelling them
   proves the individual equivalence.
5. A derived morphism is invertible exactly when all its cohomology maps are invertible
   (`lem-weil-pbc-derived-plus-iso-on-cohomology`). Exact inverse image commutes with
   cohomology (`lem-weil-pbc-exact-functor-complex-cohomology`), and an etale cover detects
   sheaf isomorphisms (`lem-weil-pbc-etale-cover-detects-iso`). Apply this to the cover
   `k i` and combine with step 4 to obtain the global equivalence. -/
theorem derivedBaseChange_target_locality
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g)
    (I : Type w) (V Xi Yi' Xi' : I → Scheme.{u})
    (j : ∀ i, V i ⟶ Y) [∀ i, AlgebraicGeometry.Etale (j i)]
    (_hcover : ∀ y : Y, ∃ (i : I) (v : V i), (j i).base v = y)
    (fi : ∀ i, Xi i ⟶ V i) (jXi : ∀ i, Xi i ⟶ X)
    (_sqj : ∀ i, IsPullback (jXi i) (fi i) f (j i))
    (k : ∀ i, Yi' i ⟶ Y') (gi : ∀ i, Yi' i ⟶ V i)
    (_sqY : ∀ i, IsPullback (k i) (gi i) g (j i))
    (kXi : ∀ i, Xi' i ⟶ X') (fi' : ∀ i, Xi' i ⟶ Yi' i)
    (_sqk : ∀ i, IsPullback (kXi i) (fi' i) f' (k i))
    (gi' : ∀ i, Xi' i ⟶ Xi i)
    (_hcomponent : ∀ i, gi' i ≫ jXi i = kXi i ≫ g')
    (sqᵢ : ∀ i, CommSq (gi' i) (fi' i) (fi i) (gi i))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (∀ i, IsPullback (gi' i) (fi' i) (fi i) (gi i)) ∧
    (∀ i,
      IsIso ((upperStar AddCommGrpCat.{u + 1} (k i)).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F))) ↔
      IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} (sqᵢ i)).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (Xi i).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          ((upperStar AddCommGrpCat.{u + 1} (jXi i)).obj F)))) ∧
    (IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor
        (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj F)) ↔
      ∀ i, IsIso ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} (sqᵢ i)).app
        ((DerivedCategory.Plus.singleFunctor
          (Sheaf (Xi i).smallEtaleTopology AddCommGrpCat.{u + 1}) 0).obj
          ((upperStar AddCommGrpCat.{u + 1} (jXi i)).obj F)))) := by
  sorry

/-- PBC descends from an etale cover of the target; the base changes are proper.
Source: Stacks Project, Tags 0EZR and 0A4F
(blueprint: lemma-weil-pbc-target-locality).

Proof:
1. Each `fi i` is a base change of the proper `f`, hence proper
   (`lem-weil-pbc-proper-base-change`).
2. Fix any base change square of `f` and any torsion abelian sheaf `F`. Its inverse image
   along `jXi i` is torsion (`lem-weil-pbc-inverse-image-torsion`).
3. Form the cartesian cube of the preceding statement. The PBC hypothesis on `fi i`
   makes the localized exchange map for this restricted sheaf invertible.
4. The global equivalence of `derivedBaseChange_target_locality` makes the original
   exchange map invertible. Since the square and torsion sheaf were arbitrary, this is
   `HasTorsionAbelianBaseChange f` (`def-weil-pbc-property`). No converse is asserted. -/
theorem hasTorsionAbelianBaseChange_of_etale_cover
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (I : Type w) (V Xi : I → Scheme.{u})
    (j : ∀ i, V i ⟶ Y) [∀ i, AlgebraicGeometry.Etale (j i)]
    (_hcover : ∀ y : Y, ∃ (i : I) (v : V i), (j i).base v = y)
    (fi : ∀ i, Xi i ⟶ V i) (jXi : ∀ i, Xi i ⟶ X)
    (_sqj : ∀ i, IsPullback (jXi i) (fi i) f (j i)) :
    (∀ i, IsProper (fi i)) ∧
      ((∀ i, HasTorsionAbelianBaseChange (fi i)) → HasTorsionAbelianBaseChange f) := by
  sorry

end AlgebraicGeometry.Etale
